package ir.transforms.memoryEncoding.split

import boogie.*
import ir.*
import ir.cilvisitor.*

// Final n bytes of "addr" are offset into allocation.
// If set to 0, addresses are treated as raw pointers.
private val me_offset_size = 32;

// First n bytes of "addr" find the allocation.
// Uses whatever is left over from offset size to fit into 64 bits.
private val me_base_size = 64 - me_offset_size;

class SplitTransform(ctx: IRContext, simplify: Boolean) extends CILVisitor {

}

def memoryEncodingDecls(): List[BDeclaration] = {
  val me_object_param = BMapVar("object", MapBType(BitVecBType(64), IntBType), Scope.Parameter)
  val me_offset_param = BMapVar("offset", MapBType(BitVecBType(64), BitVecBType(64)), Scope.Parameter)
  val me_region_param = BMapVar("region", MapBType(BitVecBType(64), IntBType), Scope.Parameter)
  val me_liveness_param = BMapVar("liveness", MapBType(IntBType, BitVecBType(2)), Scope.Parameter)
  val me_size_param = BMapVar("size", MapBType(IntBType, BitVecBType(64)), Scope.Parameter)
  val mem_param = BMapVar("mem", MapBType(BitVecBType(64), BitVecBType(8)), Scope.Parameter)
  val addr_param = BVariable("addr", BitVecBType(64), Scope.Parameter)
  val n_param = BVariable("n", BitVecBType(64), Scope.Parameter)
  val obj_param = BVariable("obj", IntBType, Scope.Parameter)

  List(
    BFunction(
      "addr_to_obj",
      List(me_object_param, addr_param),
      BVariable("r", IntBType, Scope.Local),
      Some(MapAccess(me_object_param, addr_param))
    ),
    BFunction(
      "addr_to_offset",
      List(me_offset_param, addr_param),
      BVariable("r", BitVecBType(64), Scope.Local),
      Some(MapAccess(me_offset_param, addr_param))
    ),
    BFunction(
      "addr_to_region",
      List(me_region_param, addr_param),
      BVariable("r", IntBType, Scope.Local),
      Some(MapAccess(me_region_param, addr_param))
    ),
    BFunction(
      "obj_liveness",
      List(me_liveness_param, obj_param),
      BVariable("r", BitVecBType(2), Scope.Local),
      Some(MapAccess(me_liveness_param, obj_param))
    ),
    BFunction(
      "obj_size",
      List(me_size_param, obj_param),
      BVariable("r", BitVecBType(64), Scope.Local),
      Some(MapAccess(me_size_param, obj_param))
    ),
    BFunction(
      "read_mem",
      List(mem_param, addr_param),
      BVariable("r", BitVecBType(8), Scope.Local),
      Some(MapAccess(mem_param, addr_param))
    ),
    BFunction(
      "valid",
      List(me_liveness_param, me_size_param, me_object_param, me_region_param, me_offset_param, addr_param, n_param),
      BVariable("r", BoolBType, Scope.Local),
      Some(
        BinaryBExpr(
          BoolIMPLIES,
          BinaryBExpr(
            EQ,
            BFunctionCall("addr_to_region", List(me_region_param, addr_param), IntBType, true),
            IntBLiteral(1)
          ),
          BinaryBExpr(
            BoolAND,
            BinaryBExpr(
              EQ,
              BFunctionCall(
                "obj_liveness",
                List(
                  me_liveness_param,
                  BFunctionCall("addr_to_obj", List(me_object_param, addr_param), IntBType, true)
                ),
                BitVecBType(2),
                true
              ),
              BitVecBLiteral(1, 2)
            ),
            BinaryBExpr(
              BoolAND,
              BinaryBExpr(
                BVULE,
                BitVecBLiteral(0, 64),
                BFunctionCall("addr_to_offset", List(me_offset_param, addr_param), BitVecBType(64), true)
              ),
              BinaryBExpr(
                BVULE,
                BinaryBExpr(
                  BVADD,
                  BFunctionCall("addr_to_offset", List(me_offset_param, addr_param), BitVecBType(64), true),
                  n_param
                ),
                BFunctionCall(
                  "obj_size",
                  List(me_size_param, BFunctionCall("addr_to_obj", List(me_object_param, addr_param), IntBType, true)),
                  BitVecBType(64),
                  true
                )
              )
            )
          )
        )
      )
    )
  )
}
