import Encryption

/-!
# Constructed local truth tables for an NC⁰ generator

Locality, which is part of the permitted PRG interface, determines a finite
truth table for every output bit. Inconsistent patterns on repeated seed
indices get an arbitrary fixed value. Actual seed patterns are proved to
evaluate to the specified generator output. No generated pad is a prompt
input or an external preprocessing result.
-/

noncomputable section
namespace Encryption.LocalGenerator
open TransformerAC0

def localInput (generator : LocalGenerator seedLength outputLength locality)
    (output : Fin outputLength) (seed : Bits seedLength) : Bits locality :=
  fun index => seed (generator.dependency output index)

def truthTable (generator : LocalGenerator seedLength outputLength locality)
    (output : Fin outputLength) (input : Bits locality) : Bool :=
  if h : ∃ seed, generator.localInput output seed = input then
    generator.generate (Classical.choose h) output
  else false

theorem truthTable_correct (generator : LocalGenerator seedLength outputLength locality)
    (output : Fin outputLength) (seed : Bits seedLength) :
    generator.truthTable output (generator.localInput output seed) = generator.generate seed output := by
  have hexists : ∃ chosen, generator.localInput output chosen = generator.localInput output seed := ⟨seed, rfl⟩
  unfold truthTable
  rw [dif_pos hexists]
  apply generator.locality_correct
  intro index
  exact congrFun (Classical.choose_spec hexists) index

end Encryption.LocalGenerator
