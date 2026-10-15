import EncryptedMultitapeOutput
import PrivatePolynomialTime

/-!
# Derived-budget privacy for a whole polynomial-time output word

Only ordinary seed-indexed NC⁰ PRG security is imported. The source
simulation, all output-cell reads, binary encryption, plaintext output
suffix, seed exponent, pad capacity, and security reindexing are derived.
-/

noncomputable section
namespace PrivateOutput
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix EncryptedMultitapeOutput
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]

def payloadCoefficient (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol]
    (coefficient outputCoefficient exponent : ℕ) :=
  (polynomialTraceConstant tapes coefficient exponent + outputCoefficient) * vocabulary tapes State Symbol + 1

def seedLengths (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol]
    (coefficient outputCoefficient exponent : ℕ) (stretch : ℝ) : ℕ → ℕ :=
  SeedBudget.length exponent stretch (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent)

def stretchLengths (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol]
    (coefficient outputCoefficient exponent : ℕ) (stretch : ℝ) : ℕ → ℕ := fun n =>
  ⌊(seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch n : ℝ) ^ stretch⌋₊

theorem payload_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (time extra n coefficient outputCoefficient exponent : ℕ)
    (htime : time ≤ coefficient * (n + 1) ^ exponent)
    (houtput : extra + 1 ≤ outputCoefficient * (n + 1) ^ exponent) :
    eventCount machine anchor (horizonLevel (max 1 time)) extra * vocabulary tapes State Symbol + 1 ≤
      payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
  have hphase := polynomial_log_trace_bound machine anchor time n coefficient exponent htime
  have hout : extra + 1 ≤ outputCoefficient * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
    nlinarith
  have hone : 1 ≤ (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
    have hp := Nat.one_le_pow exponent (n + 1) (by omega : 1 ≤ n + 1)
    nlinarith
  have htotal : eventCount machine anchor (horizonLevel (max 1 time)) extra ≤
      (polynomialTraceConstant tapes coefficient exponent + outputCoefficient) * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
    unfold eventCount
    nlinarith
  have h := Nat.mul_le_mul_right (vocabulary tapes State Symbol) htotal
  unfold payloadCoefficient
  nlinarith

theorem capacity (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (time extra n coefficient outputCoefficient exponent : ℕ)
    (htime : time ≤ coefficient * (n + 1) ^ exponent)
    (houtput : extra + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch) :
    eventCount machine anchor (horizonLevel (max 1 time)) extra * vocabulary tapes State Symbol + 1 ≤
      stretchLengths tapes State Symbol coefficient outputCoefficient exponent stretch n := by
  apply SeedBudget.stretch_floor_capacity
    (size := (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent : ℝ))
    (by exact_mod_cast hexponent) hstretch (by positivity)
  have h := payload_bound machine anchor time extra n coefficient outputCoefficient exponent htime houtput
  simp only [Real.rpow_natCast]
  exact_mod_cast h

def chosenGenerator (coefficient outputCoefficient exponent : ℕ) (stretch : ℝ)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) :
    NC0GeneratorFamily (seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch)
      (stretchLengths tapes State Symbol coefficient outputCoefficient exponent stretch) :=
  PRGReindex.family generator (seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch)

theorem chosenGenerator_secure (coefficient outputCoefficient exponent : ℕ) (hexponent : 1 ≤ exponent)
    (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom) :
    (chosenGenerator (tapes := tapes) (State := State) (Symbol := Symbol) coefficient outputCoefficient exponent stretch generator).IsPseudorandom := by
  obtain ⟨degree, _, hinverse⟩ := SeedBudget.seed_inverse_bound
    (size := (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent : ℝ))
    (by exact_mod_cast (show 0 < exponent by omega)) hstretch
  apply PRGReindex.secure generator secure _ degree
  intro n
  exact (hinverse n).trans (Nat.pow_le_pow_left (Nat.le_succ _) degree)

def generatorPrefix {times extras : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (coefficient outputCoefficient exponent : ℕ)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (houtput : ∀ n, extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) :
    NC0GeneratorFamily (seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch)
      (fun n => eventCount machine anchor (horizonLevel (max 1 (times n))) (extras n) * vocabulary tapes State Symbol + 1) :=
  PRGRestriction.family (chosenGenerator coefficient outputCoefficient exponent stretch generator)
    (fun n => capacity machine anchor (times n) (extras n) n coefficient outputCoefficient exponent
      (htime n) (houtput n) hexponent stretch hstretch)

theorem generatorPrefix_secure {times extras : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (coefficient outputCoefficient exponent : ℕ)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (houtput : ∀ n, extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom) :
    (generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator).IsPseudorandom :=
  PRGRestriction.secure _ (chosenGenerator_secure coefficient outputCoefficient exponent hexponent stretch hstretch generator secure) _

theorem seed_resource_bounds (coefficient outputCoefficient exponent : ℕ) (hexponent : 1 ≤ exponent)
    (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch) :
    ∃ c : ℝ, (exponent : ℝ) < c ∧ c < stretch ∧ 0 < (exponent : ℝ) / c ∧ (exponent : ℝ) / c < 1 ∧
      ∀ n : ℕ, (seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch n : ℝ) ≤
        (SeedBudget.coefficient exponent stretch (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent) + 1) *
          (n + 1 : ℝ) ^ ((exponent : ℝ) / c) := by
  obtain ⟨c, hlo, hhi, hpos, hsub, hbound, _⟩ := SeedBudget.sublinear_seed_and_capacity
    (size := (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent : ℝ))
    (by exact_mod_cast hexponent) hstretch (by positivity)
  exact ⟨c, hlo, hhi, hpos, hsub, hbound⟩

theorem payload_polynomial_bound (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (time extra n coefficient outputCoefficient exponent : ℕ)
    (htime : time ≤ coefficient * (n + 1) ^ exponent)
    (houtput : extra + 1 ≤ outputCoefficient * (n + 1) ^ exponent) :
    eventCount machine anchor (horizonLevel (max 1 time)) extra * vocabulary tapes State Symbol ≤
      (2 * payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent) * (n + 1) ^ (exponent + 1) := by
  have h := payload_bound machine anchor time extra n coefficient outputCoefficient exponent htime houtput
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have hl := Nat.log_le_self 2 (n + 1); omega
  have hp := Nat.mul_le_mul_left
    (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent * (n + 1) ^ exponent) hlog
  rw [pow_succ]
  nlinarith

def model {times extras : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (outputTape : Fin tapes) (cells : ∀ n, Fin (extras n + 1) → ℤ) (bit : Symbol → Bool)
    (coefficient outputCoefficient exponent : ℕ)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (houtput : ∀ n, extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :=
  EncryptedMultitapeOutput.model machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n) bit
    ((generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator).generator n)

theorem output_at_source_time {times extras : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ∀ n, Fin (extras n + 1) → ℤ) (bit : Symbol → Bool)
    (coefficient outputCoefficient exponent : ℕ)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (houtput : ∀ n, extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) (input : Bits n)
    (seed : Bits (seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch n)) (output : Fin (extras n + 1))
    (terminal : ∀ symbols, machine.transition
      (machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state symbols =
      ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine (bitTape blank bitSymbol inputTape input))).state,
        symbols, fun _ => Direction.stay)) :
    (model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).generatedToken
      (EncryptedMultitapeOutput.inputEncoding machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n)
        (bitTape blank bitSymbol inputTape input) seed)
      ⟨eventCount machine anchor (horizonLevel (max 1 (times n))) (extras n) * vocabulary tapes State Symbol + 1 + output.val, by
        change eventCount machine anchor (horizonLevel (max 1 (times n))) (extras n) * vocabulary tapes State Symbol + 1 + output.val <
          eventCount machine anchor (horizonLevel (max 1 (times n))) (extras n) * vocabulary tapes State Symbol + extras n + 2
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (EncryptedMatrix.answerPacket 2
        (bit ((machine.run (times n) (MultitapeEfficientPhase.sourceInitial machine
          (bitTape blank bitSymbol inputTape input))).tape outputTape (cells n output)))) := by
  unfold model
  rw [EncryptedMultitapeOutput.generated_output]
  rw [machine.terminal_run_after _ (times n) _
    ((Nat.le_max_right 1 (times n)).trans (horizon_covers (max 1 (times n)))) terminal]

theorem no_readability {times extras : ℕ → ℕ} {codeWidth : ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (bitSymbol : Bool → Symbol) (inputTape outputTape : Fin tapes) (cells : ∀ n, Fin (extras n + 1) → ℤ) (bit : Symbol → Bool)
    (coefficient outputCoefficient exponent : ℕ)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (houtput : ∀ n, extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom)
    (encoding : ProtocolSerialization.Encoding codeWidth)
    (monitor : PolynomialMonitorFamily (fun n =>
      (eventCount machine anchor (horizonLevel (max 1 (times n))) (extras n) * vocabulary tapes State Symbol + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits n)) (predicate : Bits n → Bool),
      predictionSuccess distribution
        (fun input seed => EncryptedReadout.encodedTrace
          (originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n))
          (originalTransition machine blank)
          ((generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator).generator n)
          (sources machine anchor (horizonLevel (max 1 (times n)))) (decode machine blank outputTape bit) encoding
          (plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n) (bitTape blank bitSymbol inputTape input)) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n :=
  EncryptedReadout.no_readability
    (fun n => originalSchedule machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n))
    (originalTransition machine blank) (fun n => sources machine anchor (horizonLevel (max 1 (times n))))
    (decode machine blank outputTape bit)
    (fun n input => plainPrompt machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n) (bitTape blank bitSymbol inputTape input))
    (generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator)
    (generatorPrefix_secure machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator secure)
    encoding monitor (2 * payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent) (exponent + 1)
    (fun n => payload_polynomial_bound machine anchor (times n) (extras n) n coefficient outputCoefficient exponent (htime n) (houtput n))

def contextCoefficient (tapes : ℕ) (State Symbol : Type*) [Fintype State] [Fintype Symbol]
    (coefficient outputCoefficient exponent : ℕ) (stretch : ℝ) :=
  ⌈SeedBudget.coefficient exponent stretch (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent)⌉₊ +
    2 * payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent +
    2 * vocabulary tapes State Symbol + outputCoefficient + 1

theorem context_bound {times extras : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (outputTape : Fin tapes) (cells : ∀ n, Fin (extras n + 1) → ℤ) (bit : Symbol → Bool)
    (coefficient outputCoefficient exponent : ℕ)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (houtput : ∀ n, extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :
    (model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.contextLength + 1 ≤
      contextCoefficient tapes State Symbol coefficient outputCoefficient exponent stretch *
        (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by
  unfold model
  rw [EncryptedMultitapeOutput.context_length]
  have hseed := SeedBudget.seed_polynomial_bound
    (size := (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent : ℝ))
    (by exact_mod_cast (show 0 < exponent by omega)) hstretch n
  have hp : n + 1 ≤ (n + 1) ^ exponent := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < n + 1) hexponent
  have hscale : n + 1 ≤ (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by nlinarith
  have hseed' := hseed.trans (Nat.mul_le_mul_left
    ⌈SeedBudget.coefficient exponent stretch (payloadCoefficient tapes State Symbol coefficient outputCoefficient exponent)⌉₊ hscale)
  change seedLengths tapes State Symbol coefficient outputCoefficient exponent stretch n ≤ _ at hseed'
  have htrace := payload_bound machine anchor (times n) (extras n) n coefficient outputCoefficient exponent (htime n) (houtput n)
  have hout := houtput n
  have hout' : extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent * (Nat.log 2 (n + 1) + 1) := by nlinarith
  unfold contextCoefficient
  nlinarith

/-- Both matrix dimension and the paper's exact parameter count are
polynomial, with constants independent of input length and seed values. -/
theorem polynomial_resources {times extras : ℕ → ℕ}
    (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (outputTape : Fin tapes) (cells : ∀ n, Fin (extras n + 1) → ℤ) (bit : Symbol → Bool)
    (coefficient outputCoefficient exponent : ℕ)
    (htime : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent)
    (houtput : ∀ n, extras n + 1 ≤ outputCoefficient * (n + 1) ^ exponent)
    (hexponent : 1 ≤ exponent) (stretch : ℝ) (hstretch : (exponent : ℝ) < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ^ (exponent + 1) ∧
      (model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ (2 * (exponent + 1)) := by
  let D := RoutedMatrix.dimensionConstant (EncryptedMatrix.packetCount 2 + 1)
    (outputHeads tapes State Symbol generator.locality) (outputOpcodes tapes State Symbol generator.locality)
  let P := 3 * (EncryptedMatrix.packetCount 2 + 1) * D +
    4 * (3 * outputHeads tapes State Symbol generator.locality + 2) * D ^ 2
  let C := 2 * contextCoefficient tapes State Symbol coefficient outputCoefficient exponent stretch
  refine ⟨2 * D * C, P * C ^ 2, ?_⟩
  intro n
  have hcontext := context_bound machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n
  have hlog : Nat.log 2 (n + 1) + 1 ≤ 2 * (n + 1) := by have h := Nat.log_le_self 2 (n + 1); omega
  have hscale := Nat.mul_le_mul_left
    (contextCoefficient tapes State Symbol coefficient outputCoefficient exponent stretch * (n + 1) ^ exponent) hlog
  have hwindow : (model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.contextLength + 1 ≤
      C * (n + 1) ^ (exponent + 1) := by
    dsimp [C]
    rw [pow_succ]
    nlinarith
  have hdim := EncryptedMultitapeOutput.dimension_linear machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n) bit
    ((generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator).generator n)
  have hpar := EncryptedMultitapeOutput.parameters_quadratic machine anchor blank (horizonLevel (max 1 (times n))) outputTape (cells n) bit
    ((generatorPrefix machine anchor coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator).generator n)
  change (model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.hiddenWidth ≤
    2 * D * ((model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.contextLength + 1) at hdim
  change (model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.parameterCount ≤
    P * ((model machine anchor blank outputTape cells bit coefficient outputCoefficient exponent htime houtput hexponent stretch hstretch generator n).architecture.contextLength + 1) ^ 2 at hpar
  constructor
  · exact hdim.trans (by nlinarith [Nat.mul_le_mul_left (2 * D) hwindow])
  · have hsquare := Nat.pow_le_pow_left hwindow 2
    have hmul := Nat.mul_le_mul_left P hsquare
    rw [mul_pow, ← pow_mul, Nat.mul_comm (exponent + 1) 2] at hmul
    exact hpar.trans (by nlinarith)

end PrivateOutput
