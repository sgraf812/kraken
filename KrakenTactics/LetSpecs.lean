/-
Let-form `@[spec]` triples: the precondition applies the postcondition to a
`let`-bound updated state.

`vcgen` builds a spec's backward rule from a zeta-reduced pattern, so the
verification condition carries the post-state as a record literal and the state
chain of a program is a nest of such literals, with no state variables and no
component equations.

The instruction actions are the ones from `Kraken/AccessorSpecs.lean` under
fresh names, so both spec styles are available in one build.
-/
import Kraken.AccessorSpecs

open Std.Internal.Do
open Std.Internal.Do.WPMonad

set_option mvcgen.warning false

namespace OpL

def movRI (r : Reg64) (i : Int64) : X64M Unit := Op.movRI r i

def addRI (r : Reg64) (i : Int64) : X64M Unit := Op.addRI r i

end OpL

section
variable (Q : Unit → MachineData → Prop) (E : X64Exit → MachineData → Prop)

@[spec] theorem OpL.movRI_spec_let (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let s' : MachineData :=
          { s with regs := s.regs.set64 r (.ofBitVec (BitVec.setWidth 64 i.toBitVec)) }
        Q () s' ⦄
      OpL.movRI r i ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [OpL.movRI, Op.movRI]; exact h

@[spec] theorem OpL.addRI_spec_let (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let s' : MachineData :=
          { s with
            regs := s.regs.set64 r
              (.ofBitVec (BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec))
            status := StatusFlags.from_result
              (BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec)
              { cf := (BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec).unsigned
                  != (BitVec.setWidth 64 i.toBitVec).unsigned
                    + (s.regs.get64 r).toBitVec.unsigned,
                af := ((BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec).take 4).unsigned
                  != ((BitVec.setWidth 64 i.toBitVec).take 4).unsigned
                    + ((s.regs.get64 r).toBitVec.take 4).unsigned,
                of := (BitVec.setWidth 64 i.toBitVec + (s.regs.get64 r).toBitVec).signed
                  != (BitVec.setWidth 64 i.toBitVec).signed
                    + (s.regs.get64 r).toBitVec.signed } }
        Q () s' ⦄
      OpL.addRI r i ⦃ Q; E ⦄ := by
  apply Triple.intro; intro s h; simp only [OpL.addRI, Op.addRI]; exact h

end
