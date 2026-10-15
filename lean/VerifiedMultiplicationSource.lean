import SchonhageRuntime
import SchonhageInitializer
import MultiplicationMachineBridge
import IntegerMultBounds.Schoenhage.SSClean

/-! A fixed, locally verified classical multiplier. Its source initializer
is proved to consist of constants and individual raw input bits. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace VerifiedMultiplicationSource
open TransformerAC0 ObliviousPhase MultitapeLiteralInitialization
open IntegerMultBounds.Schoenhage
open IntegerMultBounds.Schoenhage.Tp
open IntegerMultBounds.Schoenhage.Schedule

def program := ssProgram
def State := Option (Fin (compile (a := 0) (by decide : 0 < (64 : ℕ)) ssMain).1)
instance : Finite State := by unfold State; infer_instance
noncomputable instance : Fintype State := Fintype.ofFinite State
def machine : MultitapeTuring.Machine 64 State (Fin 4) := MultiplicationMachineBridge.machine program
def modulusWidth (n : ℕ) : ℕ := topN (SchonhageRuntime.operandWidth n)
def sources (n : ℕ) := SchonhageInitializer.sources n (modulusWidth n)
def initialTape (n : ℕ) (input : Bits (n + n)) :=
  MultitapeLiteralInitialization.initialTape (sources n) input
@[irreducible] def rootCoefficient : ℕ := costC cA cB cC0
@[irreducible] def coefficient : ℕ := SchonhageRuntime.boundCoefficient rootCoefficient
@[irreducible] def times (n : ℕ) : ℕ := SchonhageRuntime.time rootCoefficient n
def bit (symbol : Fin 4) : Bool := decide (symbol = IntegerMultBounds.Machine.bitSymbol true)

@[simp] theorem bit_symbol (value : Bool) : bit (IntegerMultBounds.Machine.bitSymbol value) = value := by
  cases value <;> decide

theorem time_bound (n : ℕ) : times n ≤ coefficient * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 2 := by
  unfold times coefficient
  exact SchonhageRuntime.time_bound rootCoefficient n

theorem initial_configuration (n : ℕ) (input : Bits (n + n)) :
    MultitapeEfficientPhase.sourceInitial machine (initialTape n input) =
      MultiplicationMachineBridge.configuration
        ((enc (a := 0) (SchonhageInitializer.bank n (modulusWidth n) input)).start program) := by
  apply MultitapeTuring.Configuration.ext
  · rfl
  · exact (SchonhageInitializer.heads_zero n (modulusWidth n) input).symm
  · exact SchonhageInitializer.sources_correct n (modulusWidth n) input

theorem full_product (n : ℕ) (input : Bits (n + n)) (position : Fin (n + n)) :
    bit ((machine.run (2 ^ horizonLevel (max 1 (times n)))
      (MultitapeEfficientPhase.sourceInitial machine (initialTape n input))).tape
        SchonhageInitializer.inputTape position.val) =
      Nat.testBit (SchonhageInitializer.rawValue n false input * SchonhageInitializer.rawValue n true input) position.val := by
  let m := SchonhageRuntime.operandWidth n
  let M := modulusWidth n
  let a := SchonhageInitializer.rawValue n false input
  let b := SchonhageInitializer.rawValue n true input
  let σ := SchonhageInitializer.bank n M input
  have hm : 1 ≤ m := Nat.le_max_left _ _
  obtain ⟨hlt, hle, hk⟩ := topN_facts hm
  change M ≤ 4 * m at hle
  have hn : n ≤ m := Nat.le_max_right _ _
  have hM : 2 * n < M := by dsimp only [M, modulusWidth]; nlinarith
  have ha := SchonhageInitializer.rawValue_lt n false input
  have hb := SchonhageInitializer.rawValue_lt n true input
  have hnM : n ≤ M := by omega
  have hab : a * b < Fm M := by
    have hp := Nat.mul_lt_mul'' ha hb
    rw [← pow_add] at hp
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show n + n ≤ M by omega)
    unfold Fm
    dsimp only [a, b]
    omega
  have haM : a < Fm M := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hnM
    unfold Fm
    dsimp only [a]
    omega
  have hbM : b < Fm M := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hnM
    unfold Fm
    dsimp only [b]
    omega
  have hstart : SSStart M a b σ := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [σ, SchonhageInitializer.bank, SchonhageInitializer.inputTape,
        tIn, ite_true]
      rw [SchonhageInitializer.paddedWord_eq n M (by omega) false input,
        SchonhageInitializer.paddedWord_eq n M (by omega) true input]
    · simp [σ, SchonhageInitializer.bank, SchonhageInitializer.inputTape,
        SchonhageInitializer.sizeTape, tIn, pN, reg]
    · intro tape hi hp
      simp only [σ, SchonhageInitializer.bank]
      rw [if_neg hi, if_neg hp]
      rfl
  obtain ⟨σ', wordSteps, hexec, hend, hwordBound⟩ := runs_ssMain_end0 (by omega) hk haM hbM σ hstart
  change wordSteps ≤ ssCost M [a, b] at hwordBound
  change SSEnd0 M (a * b % Fm M) σ' at hend
  have hcompiled := compile_correct (by decide : 0 < (64 : ℕ)) hexec (enc σ) rfl
  obtain ⟨steps, target, hsteps, hrun, hhalt, htarget⟩ := hcompiled
  have hcost := ssCost_le M a b
  have htop : cost cA cB cC0 M ≤ rootCoefficient * (4 * m + 1) *
      (Nat.size (4 * m) + 1) * (3 * Nat.size (Nat.size (4 * m)) + 1) := by
    unfold rootCoefficient
    exact cost_topN cA cB cC0 hm
  have hfinish : steps + 1 ≤ times n := by
    unfold times SchonhageRuntime.time
    change steps + 1 ≤ rootCoefficient * (4 * m + 1) * (Nat.size (4 * m) + 1) *
      (3 * Nat.size (Nat.size (4 * m)) + 1) + 2400 * m + 50001
    nlinarith
  have hpadded := MultiplicationMachineBridge.padded_run program
    ((enc σ).start program) target steps (2 ^ horizonLevel (max 1 (times n))) hrun hhalt
    (hfinish.trans ((Nat.le_max_right 1 (times n)).trans (horizon_covers _)))
  have hout : σ' tIn = ⟨[], [rwd M (a * b)]⟩ := by
    have h := hend.2.2.2.1
    rwa [Nat.mod_eq_of_lt hab] at h
  have hread := (σ' tIn).tape_word (a := 0) (w := rwd M (a * b)) (R := [])
    (by rw [hout]) position.val (by simp only [rwd_length]; have hp := position.isLt; omega)
  have hpos : (σ' tIn).pos = 0 := by rw [hout]; rfl
  simp only [hpos, zero_add] at hread
  have htape : target.tape = (enc σ').tape := congrArg IntegerMultBounds.Machine.Tapes.tape htarget
  rw [initial_configuration]
  change bit (((MultiplicationMachineBridge.machine program).run
    (2 ^ horizonLevel (max 1 (times n)))
    (MultiplicationMachineBridge.configuration ((enc σ).start program))).tape
      SchonhageInitializer.inputTape position.val) = Nat.testBit (a * b) position.val
  rw [hpadded, htape]
  change bit ((σ' tIn).tape position.val) = _
  rw [hread, bit_symbol]
  exact SchonhageInitializer.bits_getElem (M + 1) (a * b) position.val (by have hp := position.isLt; omega)

theorem middle_bit (n : ℕ) (hn : 1 ≤ n) (input : Bits (n + n)) :
    bit ((machine.run (2 ^ horizonLevel (max 1 (times n)))
      (MultitapeEfficientPhase.sourceInitial machine (initialTape n input))).tape
        SchonhageInitializer.inputTape ((n - 1 : ℕ) : ℤ)) = MultiplicationFootprint.middleBitTarget n input := by
  have h := full_product n input ⟨n - 1, by omega⟩
  simpa only [SchonhageInitializer.left_value, SchonhageInitializer.right_value,
    MultiplicationFootprint.middleBitTarget] using h

end VerifiedMultiplicationSource
