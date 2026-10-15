import NearLinearPrivateBit

/-!
# The permitted fast-multiplication import, instantiated in the private model

The same numerical model produces binary encrypted reasoning, its separator,
the central product bit, and EOS. The N log² N context and sublinear seed
hold for every original NC⁰ stretch exponent greater than one.
-/

noncomputable section
namespace PrivateMultiplication
open TransformerAC0 Encryption ObliviousPhase MultitapeMatrix

theorem encrypted_upper_bound (imported : FastMultiplication.MultitapeNLogNTheorem)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) :
    ∃ (tapes states symbols : ℕ)
      (machine : MultitapeTuring.Machine tapes (Fin states) (Fin symbols))
      (inputTape outputTape : Fin tapes) (blank : Fin symbols)
      (bitSymbol : Bool → Fin symbols) (bit : Fin symbols → Bool)
      (coefficient : ℕ) (times : ℕ → ℕ)
      (htime : ∀ N, times N ≤ coefficient * (N + 1) * (Nat.log 2 (N + 1) + 1)),
      (∃ contextCoefficient : ℕ, ∀ N,
        (NearLinearPrivateBit.model machine inputTape blank outputTape (fun N => ((N - 1 : ℕ) : ℤ)) bit
          coefficient htime stretch hstretch generator N).architecture.contextLength ≤
            contextCoefficient * (N + 1) * (Nat.log 2 (N + 1) + 1) ^ 2) ∧
      (∃ alpha seedCoefficient : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∀ N : ℕ,
        (NearLinearPrivateBit.seedLengths tapes (Fin states) (Fin symbols) coefficient stretch N : ℝ) ≤
          seedCoefficient * (N + 1 : ℝ) ^ alpha) ∧
      ∀ N, 1 ≤ N → ∀ (input : Bits (N + N))
        (seed : Bits (NearLinearPrivateBit.seedLengths tapes (Fin states) (Fin symbols) coefficient stretch N)),
        ∀ output : Fin 2,
          (NearLinearPrivateBit.model machine inputTape blank outputTape (fun N => ((N - 1 : ℕ) : ℤ)) bit
            coefficient htime stretch hstretch generator N).generatedToken
            (NearLinearPrivateBit.inputEncoding machine inputTape blank outputTape (fun N => ((N - 1 : ℕ) : ℤ)) coefficient stretch N
              (bitTape blank bitSymbol inputTape input) seed)
            ⟨NearLinearPrivateBit.payloadLength (times := times) machine inputTape N + 1 + output.val, by
              change NearLinearPrivateBit.payloadLength (times := times) machine inputTape N + 1 + output.val <
                NearLinearPrivateBit.payloadLength (times := times) machine inputTape N + 3
              have h := output.isLt; omega⟩ =
          ProtocolMatrix.dataToken (EncryptedFiniteReadout.result (NearLinearPrivateBit.outputCode
            (if output = 0 then some (MultiplicationFootprint.middleBitTarget N input) else none))) := by
  obtain ⟨tapes, states, symbols, machine, inputTape, outputTape, blank, bitSymbol, bit,
    halted, coefficient, times, _, _, _, htime, hterminal, hcorrect⟩ := imported
  refine ⟨tapes, states, symbols, machine, inputTape, outputTape, blank, bitSymbol, bit, coefficient, times, htime, ?_, ?_, ?_⟩
  · exact ⟨_, NearLinearPrivateBit.context_bound machine inputTape blank outputTape (fun N => ((N - 1 : ℕ) : ℤ)) bit
      coefficient htime stretch hstretch generator⟩
  · obtain ⟨alpha, hpos, hsub, hbound⟩ := LogSquaredSeedBudget.sublinear
      (size := (NearLinearPrivateBit.payloadCoefficient tapes (Fin states) (Fin symbols) coefficient : ℝ)) hstretch
    exact ⟨alpha, _, hpos, hsub, hbound⟩
  · intro N hN input seed output
    rw [NearLinearPrivateBit.generated_output]
    change ProtocolMatrix.dataToken (EncryptedFiniteReadout.result (NearLinearPrivateBit.outputCode
      (if output = 0 then some (bit ((machine.run (2 ^ horizonLevel (max 1 (times N)))
        (FastMultiplication.initialConfiguration machine inputTape blank bitSymbol input)).tape outputTape ((N - 1 : ℕ) : ℤ))) else none))) = _
    rw [machine.terminal_run_after _ (times N) _
      ((Nat.le_max_right 1 (times N)).trans (horizon_covers (max 1 (times N))))
      (hterminal _ (hcorrect N input).1)]
    rw [(hcorrect N input).2 ⟨N - 1, by omega⟩]
    rw [FastMultiplication.middleBit_eq N hN input]

end PrivateMultiplication
