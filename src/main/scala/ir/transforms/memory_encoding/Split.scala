package ir.transforms.memoryEncoding.split

import boogie.*
import ir.*
import ir.cilvisitor.*
import scala.math.pow

// Final n bytes of "addr" are offset into allocation.
// If set to 0, addresses are treated as raw pointers.
private val offset_size = 32;

// First n bytes of "addr" find the allocation.
// Uses whatever is left over from offset size to fit into 64 bits.
private val base_size = 64 - offset_size;

private val me_alloc_live_map = GlobalVar("me_alloc_live", MapType(BitVecType(64), BitVecType(2)))
private val me_alloc_size_map = GlobalVar("me_alloc_size", MapType(BitVecType(64), BitVecType(64)))
private val me_addr_is_heap_map = GlobalVar("me_addr_is_heap", MapType(BitVecType(64), BoolType))
private val mem = SharedMemory("mem", 64, 8)

private def disjoint(addr1: Expr, addr2: Expr): Expr =
  FApplyExpr("me_alloc_disjoint", Seq(addr1, addr2), BoolType)
private def bDisjoint(addr1: BExpr, addr2: BExpr): BExpr =
  BFunctionCall("me_alloc_disjoint", List(addr1, addr2), BoolBType)

private def addrIsHeap(map: Expr, addr: Expr): Expr =
  FApplyExpr("me_addr_is_heap", Seq(map, addr), BoolType)
private def bAddrIsHeap(map: BExpr, addr: BExpr): BExpr =
  BFunctionCall("me_addr_is_heap", List(map, addr), BoolBType)

private def allocLive(map: Expr, addr: Expr): Expr =
  FApplyExpr("me_alloc_live", Seq(map, addr), BitVecType(2))
private def bAllocLive(map: BExpr, addr: BExpr): BExpr =
  BFunctionCall("me_alloc_live", List(map, addr), BitVecBType(2))
private def validAccess(is_heap: Expr, alloc_size: Expr, alloc_live: Expr, addr: Expr, size: Expr): Expr =
  FApplyExpr("me_valid_access", Seq(is_heap, alloc_size, alloc_live, addr, size), BoolType)
private def bValidAccess(is_heap: BExpr, alloc_size: BExpr, alloc_live: BExpr, addr: BExpr, size: BExpr): BExpr =
  BFunctionCall("me_valid_access", List(is_heap, alloc_size, alloc_live, addr, size), BoolBType)

private def addrOffset(addr: Expr): Expr =
  FApplyExpr("me_addr_offset", Seq(addr), BitVecType(64))
private def bAddrOffset(addr: BExpr): BExpr =
  BFunctionCall("me_addr_offset", List(addr), BitVecBType(64))

private def addrBase(addr: Expr): Expr =
  FApplyExpr("me_addr_base", Seq(addr), BitVecType(64))
private def bAddrBase(addr: BExpr): BExpr =
  BFunctionCall("me_addr_base", List(addr), BitVecBType(64))

private def allocSize(map: Expr, addr: Expr): Expr =
  FApplyExpr("me_alloc_size", Seq(map, addr), BitVecType(64))
private def bAllocSize(map: BExpr, addr: BExpr): BExpr =
  BFunctionCall("me_alloc_size", List(map, addr), BitVecBType(64))

private def liveUpdate(map: Expr, idx: Expr, value: Expr): Expr =
  FApplyExpr("me_alloc_live_update", Seq(map, idx, value), MapType(BitVecType(64), BitVecType(2)))
private def bLiveUpdate(map: BExpr, idx: BExpr, value: BExpr): BExpr =
  BFunctionCall("me_alloc_live_update", List(map, idx, value), MapBType(BitVecBType(64), BitVecBType(2)))

private def sizeUpdate(map: Expr, idx: Expr, value: Expr): Expr =
  FApplyExpr("me_alloc_size_update", Seq(map, idx, value), MapType(BitVecType(64), BitVecType(64)))
private def bSizeUpdate(map: BExpr, idx: BExpr, value: BExpr): BExpr =
  BFunctionCall("me_alloc_size_update", List(map, idx, value), MapBType(BitVecBType(64), BitVecBType(64)))

private def in_bounds(lower: Expr, upper: Expr, n: Expr) =
  BinaryExpr(BoolAND, BinaryExpr(BVULE, lower, n), BinaryExpr(BVULT, n, upper))

private val i = LocalVar("i", BitVecType(64))

private val fresh_bv = BitVecLiteral(0, 2);
private val live_bv = BitVecLiteral(1, 2);
private val dead_bv = BitVecLiteral(2, 2);

private def implies_else(cond: Expr, true_br: Expr, false_br: Expr) = BinaryExpr(
  BoolAND,
  BinaryExpr(BoolIMPLIES, cond, true_br),
  BinaryExpr(BoolIMPLIES, UnaryExpr(BoolNOT, cond), false_br)
)

class SplitTransform(ctx: IRContext, simplify: Boolean) extends CILVisitor {
  private var global_addresses = ctx.symbols.flatMap(s => Range(s.value.intValue, s.value.intValue + s.size)).toSet

  private def r(n: Int) = if simplify then LocalVar(s"R${n}_out", BitVecType(64))
  else Register(s"R$n", 64)

  private def old_r(n: Int) = if simplify then LocalVar(s"R${n}_in", BitVecType(64)) else OldExpr(Register(s"R$n", 64))

  private def old_gamma_r(n: Int) =
    if simplify then LocalVar(s"R${n}_in", BitVecType(64)).toGamma else Old(Register(s"R$n", 64).toGamma)

  // for preconditions, aka no OLD and maps to #Rn_in with simplify
  private def pre_r(n: Int) = if simplify then LocalVar(s"R${n}_in", BitVecType(64))
  else Register(s"R$n", 64)

  private def transform_malloc(p: Procedure) = {
    p.modifies ++= Set(me_alloc_live_map, me_alloc_size_map)
    if !simplify then p.modifies ++= Set(Register("R0", 64))

    p.requires ++= List(BinaryBExpr(EQ, pre_r(0).toGamma, TrueBLiteral))

    p.requiresExpr ++= List(
      // Cant malloc 0 or less bytes
      BinaryExpr(BVUGT, pre_r(0), BitVecLiteral(0, 64)),
      // Malloc at most 2^offset_size - 1 bytes
      BinaryExpr(BVULE, pre_r(0), BitVecLiteral((BigInt(pow(2, offset_size).toLong) - 1), 64))
    )

    p.ensures ++= List(BinaryBExpr(EQ, r(0).toGamma, TrueBLiteral))

    p.ensuresExpr ++= List(
      BinaryExpr(BVUGT, BinaryExpr(BVADD, r(0), old_r(0)), r(0)),
      // Size mapping for returned pointer matches input size:
      BinaryExpr(EQ, me_alloc_size_map, sizeUpdate(OldExpr(me_alloc_size_map), r(0), old_r(0))),
      // Returned address is a base address:
      BinaryExpr(EQ, addrOffset(r(0)), BitVecLiteral(0, 64)),
      BinaryExpr(EQ, addrBase(r(0)), r(0)),
      // Returned address is on formerly fresh space:
      BinaryExpr(EQ, OldExpr(allocLive(me_alloc_live_map, r(0))), fresh_bv),
      // Returned address is on now live space:
      BinaryExpr(EQ, me_alloc_live_map, liveUpdate(OldExpr(me_alloc_live_map), r(0), live_bv)),
      // All other lives are unchanged:
      // Address is on heap:
      OldExpr(addrIsHeap(me_addr_is_heap_map, r(0))),

      // This is ensured by the above:
      // validAccess(me_addr_is_heap_map, me_alloc_size_map, me_alloc_live_map, r(0), old_r(0))
    )
  }

  private def transform_free(p: Procedure) = {
    p.modifies ++= Set(me_alloc_live_map)

    p.requiresExpr ++= List(
      // Only free a heap value
      addrIsHeap(me_addr_is_heap_map, pre_r(0)),
      // Free only at base of region:
      BinaryExpr(EQ, addrOffset(pre_r(0)), BitVecLiteral(0, 64)),
      // Object must be alive:
      BinaryExpr(EQ, allocLive(me_alloc_live_map, pre_r(0)), live_bv)
    )

    // Freeing requires fully high gamma
    p.requires ++= List(
      ForAll(
        List(i.toBoogie),
        BinaryBExpr(
          BoolIMPLIES,
          in_bounds(
            addrBase(pre_r(0)),
            BinaryExpr(BVADD, addrBase(pre_r(0)), allocSize(me_alloc_size_map, pre_r(0))),
            i
          ).toBoogie,
          BinaryBExpr(EQ, MapAccess(mem.toGamma, i.toBoogie), TrueBLiteral)
        )
      )
    )

    // Ensures liveness is dead for the object
    p.ensuresExpr ++= List(BinaryExpr(EQ, allocLive(me_alloc_live_map, pre_r(0)), dead_bv))
  }

  private def transform_main(p: Procedure) = {
    p.requires ++= List()

    p.requiresExpr ++= List(
      // Cheaty way to carve out some heap pointers that wont conflict:
      QuantifierExpr(
        QuantifierSort.forall,
        LambdaExpr(
          List(i),
          implies_else(
            BinaryExpr(BVULE, i, BitVecLiteral(global_addresses.max, 64)),
            UnaryExpr(BoolNOT, addrIsHeap(me_addr_is_heap_map, i)),
            addrIsHeap(me_addr_is_heap_map, i)
          )
        ),
        triggers = List(
          List(addrIsHeap(me_addr_is_heap_map, i)),
          // These are probably unecessary:
          List(allocLive(me_alloc_live_map, i)),
          List(allocSize(me_alloc_size_map, i)),
          List(addrBase(i)),
          List(addrOffset(i)),
        )
      ),
      // Ensure all heap addresses are initially fresh:
      QuantifierExpr(
        QuantifierSort.forall,
        LambdaExpr(
          List(i),
          BinaryExpr(
            BoolIMPLIES,
            addrIsHeap(me_addr_is_heap_map, i),
            BinaryExpr(EQ, allocLive(me_alloc_live_map, i), fresh_bv)
          )
        ),
        triggers = List(List(allocLive(me_alloc_live_map, i)))
      ),
      QuantifierExpr(
        QuantifierSort.forall,
        LambdaExpr(
          List(i),
          BinaryExpr(
            BoolIMPLIES,
            UnaryExpr(BoolNOT, addrIsHeap(me_addr_is_heap_map, i)),
            BinaryExpr(EQ, allocLive(me_alloc_live_map, i), dead_bv)
          )
        ),
        triggers = List(List(allocLive(me_alloc_live_map, i)))
      )
    )
  }

  override def vstmt(s: Statement) = {
    s match {
      case s: MemoryStore => {
        val size = BitVecLiteral(s.size / 8, 64);
        ChangeTo(
          List(
            Assert(
              validAccess(me_addr_is_heap_map, me_alloc_size_map, me_alloc_live_map, s.index, size),
              comment = Some("Requires Valid Memory")
            ),
            s
          )
        )
      }
      case s: MemoryLoad => {
        val size = BitVecLiteral(s.size / 8, 64);
        ChangeTo(
          List(
            Assert(
              validAccess(me_addr_is_heap_map, me_alloc_size_map, me_alloc_live_map, s.index, size),
              comment = Some("Requires Valid Memory")
            ),
            s
          )
        )
      }
      case _ => {
        DoChildren()
      }
    }
  }

  override def vproc(p: Procedure) = {
    p.procName match {
      case "malloc" => transform_malloc(p)
      case "free" => transform_free(p)
      case "main" => transform_main(p)
      // case "memset" => transform_memset(p)
      // case "strlen" => transform_strlen(p)
      // case "memcpy" => transform_memcpy(p)
      case _ => {}
    }

    DoChildren()
  }
}

def memoryEncodingDecls(): List[BDeclaration] = {
  val alloc_live_param = BMapVar("alloc_live", MapBType(BitVecBType(64), BitVecBType(2)), Scope.Parameter)
  val r_alloc_live_param = BMapVar("r_alloc_live", MapBType(BitVecBType(64), BitVecBType(2)), Scope.Parameter)
  val alloc_size_param = BMapVar("alloc_size", MapBType(BitVecBType(64), BitVecBType(64)), Scope.Parameter)
  val r_alloc_size_param = BMapVar("r_alloc_size", MapBType(BitVecBType(64), BitVecBType(64)), Scope.Parameter)
  val addr_is_heap_param = BMapVar("addr_is_heap", MapBType(BitVecBType(64), BoolBType), Scope.Parameter)
  val mem_param = BMapVar("mem", MapBType(BitVecBType(64), BitVecBType(8)), Scope.Parameter)

  val addr_param = BVariable("addr", BitVecBType(64), Scope.Parameter)
  val addr_param2 = BVariable("addr2", BitVecBType(64), Scope.Parameter)
  val offset_param = BVariable("offset", BitVecBType(64), Scope.Parameter)
  val base_param = BVariable("base", BitVecBType(64), Scope.Parameter)

  val size_param = BVariable("size", BitVecBType(64), Scope.Parameter)
  val live_param = BVariable("live", BitVecBType(2), Scope.Parameter)
  val bool_r_param = BVariable("r", BoolBType, Scope.Parameter)

  List(
    BDataTypeDecl(
      "mem_encoding",
      List(BDataTypeConstructor("MemEncoding", List(addr_is_heap_param)))
    ),
    BFunction(
      "me_addr_offset",
      List(addr_param),
      offset_param,
      Some(BinaryBExpr(BVCONCAT, BitVecBLiteral(0, 64 - offset_size), BVExtract(offset_size, 0, addr_param))),
      attributes = List(BAttribute("inline", Some("true")))
    ),
    BFunction(
      "me_addr_base",
      List(addr_param),
      base_param,
      Some(BinaryBExpr(BVCONCAT, BVExtract(64, 64 - base_size, addr_param), BitVecBLiteral(0, 64 - base_size))),
      attributes = List(BAttribute("inline", Some("true")))
    ),
    BFunction(
      "me_alloc_disjoint",
      List(addr_param, addr_param2),
      bool_r_param,
      Some(BinaryBExpr(NEQ, bAddrBase(addr_param), bAddrBase(addr_param2))),
      attributes = List(BAttribute("inline", Some("true")))
    ),
    BFunction(
      "me_addr_is_heap",
      List(addr_is_heap_param, addr_param),
      bool_r_param,
      Some(MapAccess(addr_is_heap_param, addr_param)),
      attributes = List(BAttribute("inline", Some("true")))
    ),
    BFunction(
      "me_alloc_size",
      List(alloc_size_param, addr_param),
      size_param,
      Some(MapAccess(alloc_size_param, bAddrBase(addr_param))),
      attributes = List(BAttribute("inline", Some("true")))
    ),
    BFunction(
      "me_alloc_live",
      List(alloc_live_param, addr_param),
      live_param,
      Some(MapAccess(alloc_live_param, bAddrBase(addr_param))),
      attributes = List(BAttribute("inline", Some("true")))
    ),
    BFunction(
      "me_alloc_live_update",
      List(alloc_live_param, addr_param, live_param),
      r_alloc_live_param,
      Some(MapUpdate(alloc_live_param, addr_param, live_param)),
      attributes = List(BAttribute("inline", Some("true")))
    ),
    BFunction(
      "me_alloc_size_update",
      List(alloc_size_param, addr_param, size_param),
      r_alloc_size_param,
      Some(MapUpdate(alloc_size_param, addr_param, size_param)),
      attributes = List(BAttribute("inline", Some("true")))
    ),
// private def liveUpdate(map: Expr, idx: Expr): Expr =
//   FApplyExpr("me_alloc_live_update", Seq(map, idx), MapType(BitVecType(64), BitVecType(2)))
// private def liveUpdate(map: BExpr, idx: BExpr): BExpr =
//   BFunctionCall("me_alloc_live_update", List(map, idx), MapBType(BitVecBType(64), BitVecBType(2)))
    BFunction(
      "me_valid_access",
      List(addr_is_heap_param, alloc_size_param, alloc_live_param, addr_param, size_param),
      bool_r_param,
      Some(
        BinaryBExpr(
          BoolIMPLIES,
          bAddrIsHeap(addr_is_heap_param, addr_param),
          BinaryBExpr(
            BoolAND,
            BinaryBExpr(EQ, bAllocLive(alloc_live_param, addr_param), live_bv.toBoogie),
            BinaryBExpr(
              BVULE,
              BinaryBExpr(BVADD, bAddrOffset(addr_param), size_param),
              bAllocSize(alloc_size_param, addr_param)
            )
          )
        )
      ),
      attributes = List(BAttribute("inline", Some("true")))
    )
    //   BFunction(
    //     "addr_to_obj",
    //     List(me_object_param, addr_param),
    //     BVariable("r", IntBType, Scope.Local),
    //     Some(MapAccess(me_object_param, addr_param))
    //   ),
    //   BFunction(
    //     "addr_to_offset",
    //     List(me_offset_param, addr_param),
    //     BVariable("r", BitVecBType(64), Scope.Local),
    //     Some(MapAccess(me_offset_param, addr_param))
    //   ),
    //   BFunction(
    //     "addr_to_region",
    //     List(me_region_param, addr_param),
    //     BVariable("r", IntBType, Scope.Local),
    //     Some(MapAccess(me_region_param, addr_param))
    //   ),
    //   BFunction(
    //     "obj_liveness",
    //     List(me_liveness_param, obj_param),
    //     BVariable("r", BitVecBType(2), Scope.Local),
    //     Some(MapAccess(me_liveness_param, obj_param))
    //   ),
    //   BFunction(
    //     "obj_size",
    //     List(me_size_param, obj_param),
    //     BVariable("r", BitVecBType(64), Scope.Local),
    //     Some(MapAccess(me_size_param, obj_param))
    //   ),
    //   BFunction(
    //     "read_mem",
    //     List(mem_param, addr_param),
    //     BVariable("r", BitVecBType(8), Scope.Local),
    //     Some(MapAccess(mem_param, addr_param))
    //   ),
    //   BFunction(
    //     "valid",
    //     List(me_liveness_param, me_size_param, me_object_param, me_region_param, me_offset_param, addr_param, n_param),
    //     BVariable("r", BoolBType, Scope.Local),
    //     Some(
    //       BinaryBExpr(
    //         BoolIMPLIES,
    //         BinaryBExpr(
    //           EQ,
    //           BFunctionCall("addr_to_region", List(me_region_param, addr_param), IntBType, true),
    //           IntBLiteral(1)
    //         ),
    //         BinaryBExpr(
    //           BoolAND,
    //           BinaryBExpr(
    //             EQ,
    //             BFunctionCall(
    //               "obj_liveness",
    //               List(
    //                 me_liveness_param,
    //                 BFunctionCall("addr_to_obj", List(me_object_param, addr_param), IntBType, true)
    //               ),
    //               BitVecBType(2),
    //               true
    //             ),
    //             BitVecBLiteral(1, 2)
    //           ),
    //           BinaryBExpr(
    //             BoolAND,
    //             BinaryBExpr(
    //               BVULE,
    //               BitVecBLiteral(0, 64),
    //               BFunctionCall("addr_to_offset", List(me_offset_param, addr_param), BitVecBType(64), true)
    //             ),
    //             BinaryBExpr(
    //               BVULE,
    //               BinaryBExpr(
    //                 BVADD,
    //                 BFunctionCall("addr_to_offset", List(me_offset_param, addr_param), BitVecBType(64), true),
    //                 n_param
    //               ),
    //               BFunctionCall(
    //                 "obj_size",
    //                 List(me_size_param, BFunctionCall("addr_to_obj", List(me_object_param, addr_param), IntBType, true)),
    //                 BitVecBType(64),
    //                 true
    //               )
    //             )
    //           )
    //         )
    //       )
    //     )
    //   )
  )
}
