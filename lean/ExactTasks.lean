import ExactFoldTrace
import PositiveAdditionFootprint

/-! # Exact-vocabulary task outputs and the footprint of those same matrices -/
noncomputable section
set_option maxHeartbeats 1200000
namespace ExactTasks
open TransformerAC0 Encryption TaskReductions ElementaryTaskUpper ExactTaskAlphabet
variable {n : ℕ}

def boolPairing : Bool ≃ Bool × Unit where
  toFun bit := (bit, ())
  invFun pair := pair.1
  left_inv _ := rfl
  right_inv pair := by cases pair with | mk bit unitValue => cases unitValue; rfl

theorem parity_algebra (input : Bits n) :
    binaryAlphabet.readBit (binaryAlphabet.output (EncryptedFold.outputCode
      (some ((List.ofFn input).foldl Bool.xor false)))) = Tal.parity (fun i => (boolPairing (input i)).1) := by
  change binaryAlphabet.readBit (binaryOutput (boolCode (some _))) = _
  rw [binaryOutput_some]
  change binaryAlphabet.readBit (binaryAlphabet.bit ((List.ofFn input).foldl Bool.xor false)) = _
  rw [binaryAlphabet.readBit_bit]
  exact xorFold_parity input

def parityModel (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :=
  ExactFold.privateModel binaryAlphabet false Bool.xor stretch hstretch generator binaryAlphabet.readBit n

theorem parity_output (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (input : Bits n)
    (seed : Bits (EncryptedFold.seedLengths Bool Bool stretch n)) (output : Fin 2) :
    (parityModel stretch hstretch generator n).generatedToken
      (ExactFold.inputEncoding binaryAlphabet false Bool.xor input seed)
      ⟨EncryptedFold.payloadLength Bool Bool n + 1 + output.val, by
        change EncryptedFold.payloadLength Bool Bool n + 1 + output.val < EncryptedFold.payloadLength Bool Bool n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (binaryOutput (boolCode (if output = 0 then some (Tal.parity input) else none))) := by
  rw [parityModel, ExactFold.privateModel, ExactFold.generated_output]
  rw [show (List.ofFn input).foldl Bool.xor false = Tal.parity input from xorFold_parity input]
  rfl

theorem parity_footprint (tal : Tal.FourierTailTheorem) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (hn : 1 ≤ n) :
    let G := (EncryptedFold.generatorPrefix (Control := Bool) (Alphabet := Bool) stretch hstretch generator).generator n
    let M := ExactFoldTrace.model binaryAlphabet false Bool.xor G binaryAlphabet.readBit (fun _ => false);
    -Real.logb 2 (Real.sqrt (Tal.tailBound M.fiberDepth M.fiberSize n)) - (EncryptedFold.seedLengths Bool Bool stretch n : ℝ) ≤
      (FiniteInformation.Distribution.uniform (Bits n × Bits (EncryptedFold.seedLengths Bool Bool stretch n))).mutualInformation Prod.fst
        (ExactFoldTrace.trace binaryAlphabet false Bool.xor G binaryAlphabet.readBit) :=
  ExactFoldTrace.information_lower_bound _ _ _ _ _ tal boolPairing parity_algebra hn

local instance : Fintype S5 := groupEnumeration

theorem s5_algebra (input : Fin n → S5) :
    groupAlphabet.readBit (groupAlphabet.output (EncryptedFold.outputCode
      (some ((List.ofFn input).foldl (· * ·) (1 : S5))))) = Tal.parity (fun i => (s5Pairing (input i)).1) := by
  change groupReadBit (groupOutput (groupOptionCode (some _))) = _
  rw [groupOutput_some]
  simp only [groupReadBit, Fin.lastCases_castSucc, Equiv.symm_apply_apply, s5Pairing_fst]
  rw [← List.prod_eq_foldl, orderedProduct_ofFn, ← s5StateTrackingParity_eq_product_sign]
  rfl

def s5Model (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :=
  ExactFold.privateModel groupAlphabet (1 : S5) (· * ·) stretch hstretch generator groupReadBit n

theorem s5_output (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (input : Fin n → S5)
    (seed : Bits (EncryptedFold.seedLengths S5 S5 stretch n)) (output : Fin 2) :
    (s5Model stretch hstretch generator n).generatedToken
      (ExactFold.inputEncoding groupAlphabet (1 : S5) (· * ·) input seed)
      ⟨EncryptedFold.payloadLength S5 S5 n + 1 + output.val, by
        change EncryptedFold.payloadLength S5 S5 n + 1 + output.val < EncryptedFold.payloadLength S5 S5 n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (groupOutput (groupOptionCode (if output = 0 then some (orderedProduct input) else none))) := by
  rw [s5Model, ExactFold.privateModel, ExactFold.generated_output, ← List.prod_eq_foldl, orderedProduct_ofFn]
  rfl

theorem s5_footprint (tal : Tal.FourierTailTheorem) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (hn : 1 ≤ n) :
    let G := (EncryptedFold.generatorPrefix (Control := S5) (Alphabet := S5) stretch hstretch generator).generator n
    let M := ExactFoldTrace.model groupAlphabet (1 : S5) (· * ·) G groupReadBit (fun _ => false);
    -Real.logb 2 (Real.sqrt (Tal.tailBound M.fiberDepth M.fiberSize n)) - (EncryptedFold.seedLengths S5 S5 stretch n : ℝ) ≤
      (FiniteInformation.Distribution.uniform ((Fin n → S5) × Bits (EncryptedFold.seedLengths S5 S5 stretch n))).mutualInformation Prod.fst
        (ExactFoldTrace.trace groupAlphabet (1 : S5) (· * ·) G groupReadBit) :=
  ExactFoldTrace.information_lower_bound _ _ _ _ _ tal s5Pairing s5_algebra hn

theorem addition_algebra (input : Fin n → Fin 100) :
    additionAlphabet.readBit (additionAlphabet.output (EncryptedFold.outputCode
      (some ((List.ofFn input).foldl additionUpdate false)))) = Tal.parity (fun i => (positiveAdditionPairing100 (input i)).1) := by
  change additionAlphabet.readBit (additionOutput (boolCode (some _))) = _
  rw [additionOutput_some]
  change additionAlphabet.readBit (additionAlphabet.bit ((List.ofFn input).foldl additionUpdate false)) = _
  rw [additionAlphabet.readBit_bit, fold_addition, List.map_ofFn]
  simpa only [positiveAdditionPairing100_fst, ElementaryTaskUpper.additionBit] using
    xorFold_parity (fun i => ElementaryTaskUpper.additionBit (input i))

def additionModel (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :=
  ExactFold.privateModel additionAlphabet false additionUpdate stretch hstretch generator additionAlphabet.readBit n

theorem addition_output (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (input : Fin n → Fin 100)
    (seed : Bits (EncryptedFold.seedLengths Bool (Fin 100) stretch n)) (output : Fin 2) :
    (additionModel stretch hstretch generator n).generatedToken
      (ExactFold.inputEncoding additionAlphabet false additionUpdate input seed)
      ⟨EncryptedFold.payloadLength Bool (Fin 100) n + 1 + output.val, by
        change EncryptedFold.payloadLength Bool (Fin 100) n + 1 + output.val < EncryptedFold.payloadLength Bool (Fin 100) n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (additionOutput (boolCode
        (if output = 0 then some (additionLSB (fun i => (input i).val + 1)) else none))) := by
  rw [additionModel, ExactFold.privateModel, ExactFold.generated_output, fold_addition, List.map_ofFn]
  simp only [Function.comp_def]
  rw [show (List.ofFn (fun i => ElementaryTaskUpper.additionBit (input i))).foldl Bool.xor false =
    additionLSB (fun i => (input i).val + 1) from (xorFold_parity _).trans (addition_parity input)]
  rfl

theorem addition_footprint (tal : Tal.FourierTailTheorem) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (hn : 1 ≤ n) :
    let G := (EncryptedFold.generatorPrefix (Control := Bool) (Alphabet := Fin 100) stretch hstretch generator).generator n
    let M := ExactFoldTrace.model additionAlphabet false additionUpdate G additionAlphabet.readBit (fun _ => false);
    -Real.logb 2 (Real.sqrt (Tal.tailBound M.fiberDepth M.fiberSize n)) - (EncryptedFold.seedLengths Bool (Fin 100) stretch n : ℝ) ≤
      (FiniteInformation.Distribution.uniform ((Fin n → Fin 100) × Bits (EncryptedFold.seedLengths Bool (Fin 100) stretch n))).mutualInformation Prod.fst
        (ExactFoldTrace.trace additionAlphabet false additionUpdate G additionAlphabet.readBit) :=
  ExactFoldTrace.information_lower_bound _ _ _ _ _ tal positiveAdditionPairing100 addition_algebra hn

end ExactTasks
