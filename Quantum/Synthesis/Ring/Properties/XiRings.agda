-- The rings of Quantum.Synthesis.Ring.XiRings are commutative rings,
-- as instances of the generic results for ℤ[1/ p ]
-- (Properties.Localized) and for quadratic and cubic extensions
-- (Properties.Quadratic, Properties.Cubic).
--
-- Care is needed with the dyadic carriers. Whenever the type checker
-- compares two instance terms that are equal but not syntactically
-- so (e.g. RingOmega {𝔻} with RingOmega {Dyadic}, or an instance found
-- by unification with one found by instance search), it eta-expands
-- the ring operations and evaluates them on variables. Over 𝔻 this
-- blows up, since the dyadic addition, which aligns denominators with
-- a "with", copies its arguments when it is stuck, and the copies
-- multiply in a tower; even checking 𝔻[ω][ζ₁₆] exhausts 6 GB. Hence:
--
-- * Each instance is first defined with its type inferred (isCR-…)
--   and then given its stated type. Checking the application directly
--   against the stated type unifies with the expected type before the
--   argument is checked, which leads to such comparisons; the two types
--   only differ in the name of the carrier.
--
-- * Above 𝔻[ω] and 𝔻[2cos(π/8)], the instance arguments are given
--   explicitly, in exactly the form in which instance search finds
--   them for the stated types (as printed with --show-implicit).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.XiRings where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Integer.Base using (ℤ)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Localized
open import Quantum.Synthesis.Ring.Quadratic
open import Quantum.Synthesis.Ring.Cubic
open import Quantum.Synthesis.Ring.XiRings
open import Quantum.Synthesis.Ring.Properties
  using (isCommutativeRing-ℤ ; isCommutativeRing-ZRootTwo ; isCommutativeRing-ZOmega ;
         isCommutativeRing-DRootTwo ; isCommutativeRing-DOmega)
open import Quantum.Synthesis.Ring.Properties.Localized using (isCommutativeRing-Frac)
open import Quantum.Synthesis.Ring.Properties.Quadratic using (isCommutativeRing-Quad)
open import Quantum.Synthesis.Ring.Properties.Cubic using (isCommutativeRing-Cub)

-- ----------------------------------------------------------------------
-- * ℤ[⅓] (p = 1 + 2)

isCommutativeRing-Triadic : IsCommutativeRing (_≡_ {A = Triadic}) _+_ _*_ -_ 0# 1#
isCommutativeRing-Triadic = isCommutativeRing-Frac 1

-- ----------------------------------------------------------------------
-- * 2-power cyclotomic rings

private
  isCR-ZZeta16 : _
  isCR-ZZeta16 = isCommutativeRing-Quad {Zeta16} {ZOmega} isCommutativeRing-ZOmega

  isCR-DZeta16 : _
  isCR-DZeta16 = isCommutativeRing-Quad {Zeta16} {DOmega} isCommutativeRing-DOmega

isCommutativeRing-ZZeta16 : IsCommutativeRing (_≡_ {A = ZZeta16}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZZeta16 = isCR-ZZeta16

isCommutativeRing-DZeta16 : IsCommutativeRing (_≡_ {A = DZeta16}) _+_ _*_ -_ 0# 1#
isCommutativeRing-DZeta16 = isCR-DZeta16

private
  isCR-ZZeta32 : _
  isCR-ZZeta32 = isCommutativeRing-Quad {Zeta32} {Quadratic Zeta16 ZOmega} isCR-ZZeta16

isCommutativeRing-ZZeta32 : IsCommutativeRing (_≡_ {A = ZZeta32}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZZeta32 = isCR-ZZeta32

private
  isCR-DZeta32 : _
  isCR-DZeta32 = isCommutativeRing-Quad {Zeta32} {DZeta16}
    {{RingQuad {Zeta16} {DOmega} {{RingOmega {𝔻} {{RingDyadic}}}}
       {{GeneratorZeta16 {DOmega} {{RingOmega {𝔻} {{RingDyadic}}}} {{OmegaRingOmega {𝔻} {{RingDyadic}}}}}}}}
    {{GeneratorSqrtGen {Zeta16} {DOmega} {{RingOmega {𝔻} {{RingDyadic}}}}
       {{GeneratorZeta16 {DOmega} {{RingOmega {𝔻} {{RingDyadic}}}} {{OmegaRingOmega {𝔻} {{RingDyadic}}}}}}}}
    isCommutativeRing-DZeta16

isCommutativeRing-DZeta32 : IsCommutativeRing (_≡_ {A = DZeta32}) _+_ _*_ -_ 0# 1#
isCommutativeRing-DZeta32 = isCR-DZeta32

-- ----------------------------------------------------------------------
-- * 3-power cyclotomic rings

private
  isCR-ZZeta3 : _
  isCR-ZZeta3 = isCommutativeRing-Quad {Zeta3} {ℤ} isCommutativeRing-ℤ

  isCR-TZeta3 : _
  isCR-TZeta3 = isCommutativeRing-Quad {Zeta3} {Triadic} isCommutativeRing-Triadic

isCommutativeRing-ZZeta3 : IsCommutativeRing (_≡_ {A = ZZeta3}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZZeta3 = isCR-ZZeta3

isCommutativeRing-TZeta3 : IsCommutativeRing (_≡_ {A = TZeta3}) _+_ _*_ -_ 0# 1#
isCommutativeRing-TZeta3 = isCR-TZeta3

private
  isCR-ZZeta9 : _
  isCR-ZZeta9 = isCommutativeRing-Cub {Zeta9} {Quadratic Zeta3 ℤ} isCR-ZZeta3

  isCR-TZeta9 : _
  isCR-TZeta9 = isCommutativeRing-Cub {Zeta9} {Quadratic Zeta3 Triadic} isCR-TZeta3

isCommutativeRing-ZZeta9 : IsCommutativeRing (_≡_ {A = ZZeta9}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZZeta9 = isCR-ZZeta9

isCommutativeRing-TZeta9 : IsCommutativeRing (_≡_ {A = TZeta9}) _+_ _*_ -_ 0# 1#
isCommutativeRing-TZeta9 = isCR-TZeta9

-- ----------------------------------------------------------------------
-- * Real subfields of 2-power cyclotomic fields

private
  isCR-ZCos8 : _
  isCR-ZCos8 = isCommutativeRing-Quad {TwoCos8} {ZRootTwo} isCommutativeRing-ZRootTwo

  isCR-DCos8 : _
  isCR-DCos8 = isCommutativeRing-Quad {TwoCos8} {DRootTwo} isCommutativeRing-DRootTwo

isCommutativeRing-ZCos8 : IsCommutativeRing (_≡_ {A = ZCos8}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZCos8 = isCR-ZCos8

isCommutativeRing-DCos8 : IsCommutativeRing (_≡_ {A = DCos8}) _+_ _*_ -_ 0# 1#
isCommutativeRing-DCos8 = isCR-DCos8

private
  isCR-ZCos16 : _
  isCR-ZCos16 = isCommutativeRing-Quad {TwoCos16} {Quadratic TwoCos8 ZRootTwo} isCR-ZCos8

  isCR-DCos16 : _
  isCR-DCos16 = isCommutativeRing-Quad {TwoCos16} {DCos8}
    {{RingQuad {TwoCos8} {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{GeneratorTwoCos8 {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{RootTwoRingRootTwo {𝔻} {{RingDyadic}}}}}}}}
    {{GeneratorTwoCosHalf {TwoCos8} {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{GeneratorTwoCos8 {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{RootTwoRingRootTwo {𝔻} {{RingDyadic}}}}}}}}
    isCommutativeRing-DCos8

isCommutativeRing-ZCos16 : IsCommutativeRing (_≡_ {A = ZCos16}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZCos16 = isCR-ZCos16

isCommutativeRing-DCos16 : IsCommutativeRing (_≡_ {A = DCos16}) _+_ _*_ -_ 0# 1#
isCommutativeRing-DCos16 = isCR-DCos16

private
  isCR-ZCos32 : _
  isCR-ZCos32 = isCommutativeRing-Quad {TwoCos32} {Quadratic TwoCos16 (Quadratic TwoCos8 ZRootTwo)} isCR-ZCos16

  isCR-DCos32 : _
  isCR-DCos32 = isCommutativeRing-Quad {TwoCos32} {DCos16}
    {{RingQuad {TwoCos16} {DCos8} {{RingQuad {TwoCos8} {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{GeneratorTwoCos8 {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{RootTwoRingRootTwo {𝔻} {{RingDyadic}}}}}}}} {{GeneratorTwoCosHalf {TwoCos8} {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{GeneratorTwoCos8 {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{RootTwoRingRootTwo {𝔻} {{RingDyadic}}}}}}}}}}
    {{GeneratorTwoCosHalf {TwoCos16} {DCos8} {{RingQuad {TwoCos8} {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{GeneratorTwoCos8 {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{RootTwoRingRootTwo {𝔻} {{RingDyadic}}}}}}}} {{GeneratorTwoCosHalf {TwoCos8} {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{GeneratorTwoCos8 {DRootTwo} {{RingRootTwo {𝔻} {{RingDyadic}}}} {{RootTwoRingRootTwo {𝔻} {{RingDyadic}}}}}}}}}}
    isCommutativeRing-DCos16

isCommutativeRing-ZCos32 : IsCommutativeRing (_≡_ {A = ZCos32}) _+_ _*_ -_ 0# 1#
isCommutativeRing-ZCos32 = isCR-ZCos32

isCommutativeRing-DCos32 : IsCommutativeRing (_≡_ {A = DCos32}) _+_ _*_ -_ 0# 1#
isCommutativeRing-DCos32 = isCR-DCos32

-- ----------------------------------------------------------------------
-- * Bundles

commutativeRing-Triadic
  commutativeRing-ZZeta16 commutativeRing-DZeta16 commutativeRing-ZZeta32 commutativeRing-DZeta32
  commutativeRing-ZZeta3 commutativeRing-TZeta3 commutativeRing-ZZeta9 commutativeRing-TZeta9
  commutativeRing-ZCos8 commutativeRing-DCos8 commutativeRing-ZCos16 commutativeRing-DCos16
  commutativeRing-ZCos32 commutativeRing-DCos32 : CommutativeRing 0ℓ 0ℓ
commutativeRing-Triadic = record { isCommutativeRing = isCommutativeRing-Triadic }
commutativeRing-ZZeta16 = record { isCommutativeRing = isCommutativeRing-ZZeta16 }
commutativeRing-DZeta16 = record { isCommutativeRing = isCommutativeRing-DZeta16 }
commutativeRing-ZZeta32 = record { isCommutativeRing = isCommutativeRing-ZZeta32 }
commutativeRing-DZeta32 = record { isCommutativeRing = isCommutativeRing-DZeta32 }
commutativeRing-ZZeta3 = record { isCommutativeRing = isCommutativeRing-ZZeta3 }
commutativeRing-TZeta3 = record { isCommutativeRing = isCommutativeRing-TZeta3 }
commutativeRing-ZZeta9 = record { isCommutativeRing = isCommutativeRing-ZZeta9 }
commutativeRing-TZeta9 = record { isCommutativeRing = isCommutativeRing-TZeta9 }
commutativeRing-ZCos8 = record { isCommutativeRing = isCommutativeRing-ZCos8 }
commutativeRing-DCos8 = record { isCommutativeRing = isCommutativeRing-DCos8 }
commutativeRing-ZCos16 = record { isCommutativeRing = isCommutativeRing-ZCos16 }
commutativeRing-DCos16 = record { isCommutativeRing = isCommutativeRing-DCos16 }
commutativeRing-ZCos32 = record { isCommutativeRing = isCommutativeRing-ZCos32 }
commutativeRing-DCos32 = record { isCommutativeRing = isCommutativeRing-DCos32 }
