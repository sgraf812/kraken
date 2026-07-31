/-
Memory-op benchmarks for the `easm` discharge pipeline: a single load, and a
store followed by a reload of the same cell. The `Kraken.easm` trace reports
which discharge path closed each memory VC.
-/
import Kraken.Tactics
open Std.Internal.Do
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def loadProg : X64M Unit :=
  Op.movRM .rax (Addr.mk .rsp none (-8))

set_option trace.Kraken.easm true in
theorem load_single (s₀ : MachineData) (v : Int)
    (h_load : Mem.loadInt s₀.dmem ((Addr.mk .rsp none (-8)).eval s₀.regs) 8 = some v) :
    ⦃fun sd => sd = s₀⦄ loadProg
      ⦃fun _ s => s.regs.rax = BitVec.ofInt 64 v⦄ := by
  sym =>
    vcgen [loadProg]
    all_goals (first (easm) (skip))
    all_goals finish (splits := 40)

def storeLoadProg : X64M Unit := do
  Op.movMI (Addr.mk .rsp none (-8)) 99
  Op.movRM .rax (Addr.mk .rsp none (-8))

set_option trace.Kraken.easm true in
theorem store_load_back (s₀ : MachineData) (v : Int)
    (h_mapped : Mem.loadInt s₀.dmem ((Addr.mk .rsp none (-8)).eval s₀.regs) 8 = some v)
    (h_back : Mem.loadInt
        (Mem.storeInt s₀.dmem ((Addr.mk .rsp none (-8)).eval s₀.regs) 8 99)
        ((Addr.mk .rsp none (-8)).eval s₀.regs) 8 = some 99) :
    ⦃fun sd => sd = s₀⦄ storeLoadProg
      ⦃fun _ s => s.regs.rax = BitVec.ofInt 64 99⦄ := by
  have h99 : (BitVec.setWidth 64 ((99 : Int64)).toBitVec).toInt = 99 := by decide
  sym =>
    vcgen [storeLoadProg]
    all_goals (first (easm) (skip))
    all_goals finish (splits := 40)
