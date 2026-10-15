import EncryptedFold

/-!
# Actual private upper models for parity, full S₅, and iterated addition

The generic construction is instantiated on the full task input alphabets.
All three have linear reasoning/context, fixed precision, constant heads,
and polynomial dimension/parameter count. Only ordinary seed-indexed PRG
security is needed for the privacy conclusion of `EncryptedFold`.
-/

noncomputable section
namespace EncryptedTaskUpper
open TransformerAC0 Encryption TaskReductions ElementaryTaskUpper
variable {Control Alphabet : Type*} [Fintype Control] [Fintype Alphabet]
variable [Inhabited Control] [Inhabited Alphabet] {n : ℕ}

def decodeToken : Fin (EncryptedMatrix.packetCount 2 + Fintype.card (Option Control) + 1) → Option Control :=
  Fin.lastCases none (Fin.addCases (fun _ => none) EncryptedFold.outputCode.symm)

def outputValue (initial : Control) (update : Control → Alphabet → Control)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)
    (input : Fin n → Alphabet) (seed : Bits (EncryptedFold.seedLengths Control Alphabet stretch n)) : Option Control :=
  decodeToken ((EncryptedFold.privateModel initial update stretch hstretch generator n).generatedToken
    (EncryptedFold.inputEncoding initial update input seed)
    ⟨EncryptedFold.payloadLength Control Alphabet n + 1, by
      change EncryptedFold.payloadLength Control Alphabet n + 1 < EncryptedFold.payloadLength Control Alphabet n + 3
      omega⟩)

theorem outputValue_correct (initial : Control) (update : Control → Alphabet → Control)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)
    (input : Fin n → Alphabet) (seed : Bits (EncryptedFold.seedLengths Control Alphabet stretch n)) :
    outputValue initial update stretch hstretch generator input seed = some ((List.ofFn input).foldl update initial) := by
  unfold outputValue EncryptedFold.privateModel
  have h := EncryptedFold.generated_output initial update
    ((EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Alphabet) stretch hstretch generator).generator n) input seed (0 : Fin 2)
  have hdecode := congrArg (decodeToken (Control := Control)) h
  simpa [decodeToken, ProtocolMatrix.dataToken, EncryptedFiniteReadout.result] using hdecode

theorem eos_generated (initial : Control) (update : Control → Alphabet → Control)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)
    (input : Fin n → Alphabet) (seed : Bits (EncryptedFold.seedLengths Control Alphabet stretch n)) :
    (EncryptedFold.privateModel initial update stretch hstretch generator n).generatedToken
      (EncryptedFold.inputEncoding initial update input seed)
      ⟨EncryptedFold.payloadLength Control Alphabet n + 2, by
        change EncryptedFold.payloadLength Control Alphabet n + 2 < EncryptedFold.payloadLength Control Alphabet n + 3
        omega⟩ =
      ProtocolMatrix.dataToken (EncryptedFiniteReadout.result (EncryptedFold.outputCode (none : Option Control))) := by
  simpa only [Fin.val_one, one_ne_zero, if_false] using EncryptedFold.generated_output initial update
    ((EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Alphabet) stretch hstretch generator).generator n) input seed (1 : Fin 2)

theorem polynomial_resources (initial : Control) (update : Control → Alphabet → Control)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (EncryptedFold.privateModel initial update stretch hstretch generator n).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ∧
      (EncryptedFold.privateModel initial update stretch hstretch generator n).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ 2 := by
  let C := ⌈SeedBudget.coefficient 1 stretch (ObliviousMatrix.vocabulary Control Alphabet + 1)⌉₊ +
    4 * ObliviousMatrix.vocabulary Control Alphabet + 3
  have hcontext : ∀ n, (EncryptedFold.privateModel initial update stretch hstretch generator n).architecture.contextLength + 1 ≤ C * (n + 1) := by
    intro n
    have h := EncryptedFold.context_linear initial update stretch hstretch generator n
    dsimp [C]
    nlinarith
  simpa only [pow_one, Nat.mul_one] using EncryptedFiniteReadout.polynomial_resources
    (EncryptedFold.originalSchedule initial update) EncryptedFold.originalTransition
    (EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Alphabet) stretch hstretch generator)
    (fun n => EncryptedFold.sources n) (fun _ => EncryptedFold.decode (Control := Control) (Alphabet := Alphabet)) C 1
    (fun n => by simpa only [pow_one] using hcontext n)

theorem parity_correct (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (input : Bits n)
    (seed : Bits (EncryptedFold.seedLengths Bool Bool stretch n)) :
    outputValue false Bool.xor stretch hstretch generator input seed = some (Tal.parity input) := by
  rw [outputValue_correct]
  congr 1
  exact xorFold_parity input

local instance : Fintype S5 := Fintype.ofFinite S5

/-- The native output is the entire S₅ product, not its parity/sign quotient. -/
theorem s5_full_product_correct (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (input : Fin n → S5)
    (seed : Bits (EncryptedFold.seedLengths S5 S5 stretch n)) :
    outputValue (1 : S5) (fun a b : S5 => a * b) stretch hstretch generator input seed = some (orderedProduct input) := by
  rw [outputValue_correct]
  congr 1
  exact (List.prod_eq_foldl.symm).trans (orderedProduct_ofFn input)

theorem addition_correct (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (input : Fin n → Fin 100)
    (seed : Bits (EncryptedFold.seedLengths Bool (Fin 100) stretch n)) :
    outputValue false additionUpdate stretch hstretch generator input seed = some (additionLSB (fun i => (input i).val + 1)) := by
  rw [outputValue_correct, fold_addition, List.map_ofFn]
  congr 1
  exact (xorFold_parity (fun i => additionBit (input i))).trans (addition_parity input)

end EncryptedTaskUpper
