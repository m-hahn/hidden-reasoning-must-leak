/- Ported to the faithfulness project's pinned Lean/mathlib v4.19.0.
Upstream revision add0aca8ee0d71e68969f2cb45cf91554a50f787; original copyright/license below. -/
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

import Complexitylib.Algebraic.Interpretation
import Cslib.Computability.Circuit.Homomorphism

/-!
# Interpretation homomorphisms from CSLib

The homomorphism structure, identities, composition, and their laws are supplied
by CSLib. The names here preserve the existing public imports.
-/
namespace Algebraic

export Cslib.Circuits (Homomorphism)

namespace Homomorphism

export Cslib.Circuits.Homomorphism
  (ext id comp id_map comp_map id_comp comp_id comp_assoc)

end Homomorphism
end Algebraic
