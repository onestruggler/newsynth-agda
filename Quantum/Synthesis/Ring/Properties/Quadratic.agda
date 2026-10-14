-- If A is a commutative ring, then so is every quadratic extension
-- Quadratic G A = A[θ], θ² = s + tθ (with the ring operations of the
-- instances in Quantum.Synthesis.Ring.Quadratic), for all generators G
-- at once.
--
-- The proof is the one for A [√2] (Properties.RootTwo): the ring
-- operations are computed on polynomial expressions, and the solver
-- proves the resulting identities componentwise. Here the generator's
-- s and t are two further variables of the polynomials, so that the
-- identities hold for all s and t.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Quadratic where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong₂)

open import Instances
open import Quantum.Synthesis.Ring.Quadratic
  using (Quadratic ; Quad ; Generator ; gen-s ; gen-t ; SemiRingQuad ; RingQuad ; lift-Quad)
open import Quantum.Synthesis.Ring.Properties.Common using (CRLaws ; isCommutativeRing-from-laws)
import Quantum.Synthesis.Ring.Properties.Poly as Poly
import Quantum.Synthesis.Ring.Properties.Hom as Hom

open Quadratic using (q-a ; q-b)

module _ {G A : Set} {{RA : Ring A}} {{GA : Generator G A}}
         (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  open Poly isCR using (Polynomial ; var ; ⟦_⟧ ; ⟦_⟧↓ ; prove ; SemiRingPoly ; RingPoly)

  private
    v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : Polynomial 8
    v₀ = var zero
    v₁ = var (suc zero)
    v₂ = var (suc (suc zero))
    v₃ = var (suc (suc (suc zero)))
    v₄ = var (suc (suc (suc (suc zero))))
    v₅ = var (suc (suc (suc (suc (suc zero)))))
    v₆ = var (suc (suc (suc (suc (suc (suc zero))))))
    v₇ = var (suc (suc (suc (suc (suc (suc (suc zero)))))))

    -- Over polynomials, s and t are the variables v₆ and v₇.
    instance
      GeneratorPoly : Generator G (Polynomial 8)
      GeneratorPoly = record { gen-s = v₆ ; gen-t = v₇ }

    -- The semantics of an expression of Quadratic G (Polynomial 8).
    ⟦_⟧Q : Quadratic G (Polynomial 8) -> Vec A 8 -> Quadratic G A
    ⟦ Quad a b ⟧Q ρ = Quad (⟦ a ⟧ ρ) (⟦ b ⟧ ρ)

    -- Proving an equation of Quadratic G A componentwise with the solver.
    by : ∀ (ρ : Vec A 8) (e₁ e₂ : Quadratic G (Polynomial 8)) ->
         ⟦ q-a e₁ ⟧↓ ρ ≡ ⟦ q-a e₂ ⟧↓ ρ -> ⟦ q-b e₁ ⟧↓ ρ ≡ ⟦ q-b e₂ ⟧↓ ρ ->
         ⟦ e₁ ⟧Q ρ ≡ ⟦ e₂ ⟧Q ρ
    by ρ (Quad a b) (Quad c d) h₁ h₂ = cong₂ Quad (prove ρ a c h₁) (prove ρ b d h₂)

    -- Three generic elements, and the corresponding environment (which
    -- ends with the generator's s and t).
    X Y Z : Quadratic G (Polynomial 8)
    X = Quad v₀ v₁
    Y = Quad v₂ v₃
    Z = Quad v₄ v₅

    ρ : Quadratic G A -> Quadratic G A -> Quadratic G A -> Vec A 8
    ρ (Quad a b) (Quad c d) (Quad e f) = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ gen-s {G} ∷ gen-t {G} ∷ []

  +-assoc-Quad : ∀ (x y z : Quadratic G A) -> (x + y) + z ≡ x + (y + z)
  +-assoc-Quad x y z = by (ρ x y z) ((X + Y) + Z) (X + (Y + Z)) refl refl

  +-comm-Quad : ∀ (x y : Quadratic G A) -> x + y ≡ y + x
  +-comm-Quad x y = by (ρ x y y) (X + Y) (Y + X) refl refl

  +-identityˡ-Quad : ∀ (x : Quadratic G A) -> 0# + x ≡ x
  +-identityˡ-Quad x = by (ρ x x x) (0# + X) X refl refl

  -‿inverseˡ-Quad : ∀ (x : Quadratic G A) -> (- x) + x ≡ 0#
  -‿inverseˡ-Quad x = by (ρ x x x) ((- X) + X) 0# refl refl

  *-assoc-Quad : ∀ (x y z : Quadratic G A) -> (x * y) * z ≡ x * (y * z)
  *-assoc-Quad x y z = by (ρ x y z) ((X * Y) * Z) (X * (Y * Z)) refl refl

  *-comm-Quad : ∀ (x y : Quadratic G A) -> x * y ≡ y * x
  *-comm-Quad x y = by (ρ x y y) (X * Y) (Y * X) refl refl

  *-identityˡ-Quad : ∀ (x : Quadratic G A) -> 1# * x ≡ x
  *-identityˡ-Quad x = by (ρ x x x) (1# * X) X refl refl

  distribʳ-Quad : ∀ (x y z : Quadratic G A) -> (y + z) * x ≡ y * x + z * x
  distribʳ-Quad x y z = by (ρ x y z) ((Y + Z) * X) (Y * X + Z * X) refl refl

  isCommutativeRing-Quad : IsCommutativeRing _≡_ _+_ _*_ -_ 0# (1# {Quadratic G A})
  isCommutativeRing-Quad = isCommutativeRing-from-laws _ _ _ _ _ record
    { +-assoc = +-assoc-Quad
    ; +-comm = +-comm-Quad
    ; +-identityˡ = +-identityˡ-Quad
    ; -‿inverseˡ = -‿inverseˡ-Quad
    ; *-assoc = *-assoc-Quad
    ; *-comm = *-comm-Quad
    ; *-identityˡ = *-identityˡ-Quad
    ; distribʳ = distribʳ-Quad
    }

  commutativeRing-Quad : CommutativeRing 0ℓ 0ℓ
  commutativeRing-Quad = record { isCommutativeRing = isCommutativeRing-Quad }

  -- The constant-coefficient embedding A → A[θ] is a ring homomorphism.
  lift-Quad-isRingHom : Hom.IsRingHom (lift-Quad {G} {A})
  lift-Quad-isRingHom = record
    { multiplicative = record
      { f-* = λ a b -> by (env a b) (Quad (v₀ * v₁) 0#) (Quad v₀ 0# * Quad v₁ 0#) refl refl
      ; f-1 = refl }
    ; f-+ = λ a b -> by (env a b) (Quad (v₀ + v₁) 0#) (Quad v₀ 0# + Quad v₁ 0#) refl refl
    ; f-0 = refl
    ; f-neg = λ a -> by (env a a) (Quad (- v₀) 0#) (- Quad v₀ 0#) refl refl }
    where
      env : A -> A -> Vec A 8
      env a b = a ∷ b ∷ a ∷ a ∷ a ∷ a ∷ gen-s {G} ∷ gen-t {G} ∷ []
