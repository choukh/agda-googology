{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Universe.GeneratedCode where

-- Encode the positive generated predicate inside the existing Pi/Sigma/W/
-- equality universe. No extra constructor or universe axiom is added to U.
open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Mahlo.Archive.Legacy.Universe.External using (Fam; sup; module Close)
import Mahlo.Archive.Legacy.WellOrder.Accessible as A

subst : {X : Set} (P : X → Set) {x y : X} → x ≡ y → P x → P y
subst P refl px = px

module Encode (F : Fam → Fam) where
  open Close F

  module Rule (M : Nat → U) (Pred : Nat → Nat → U) where
    module G = A.Generate (λ x → El (M x)) (λ x y → El (Pred x y))

    labels : U
    labels = sigma nat M

    branches : El labels → U
    branches (x , mx) = sigma nat (Pred x)

    trees : U
    trees = w labels branches

    index : El trees → Nat
    index (sup (x , mx) children) = x

    -- A raw W-tree may have the wrong root label at a child. Keep that
    -- obligation in the code rather than silently treating every tree as valid.
    valid : El trees → U
    valid (sup label children) = pi (branches label) (λ edge →
      sigma (eq nat (index (children edge)) (fst edge))
        (λ _ → valid (children edge)))

    code : Nat → U
    code x = sigma trees (λ t →
      sigma (eq nat (index t) x) (λ _ → valid t))

    introduce : (x : Nat) → El (M x)
      → ((y : Nat) → El (Pred x y) → El (code y)) → El (code x)
    introduce x mx below =
      sup (x , mx) (λ edge → fst (below (fst edge) (snd edge))) ,
      refl , (λ edge → snd (below (fst edge) (snd edge)))

    tree-sound : (t : El trees) → El (valid t) → G.Generated (index t)
    tree-sound (sup (x , mx) children) correct = G.step mx (λ y edge →
      subst G.Generated (fst (correct (y , edge)))
        (tree-sound (children (y , edge)) (snd (correct (y , edge)))))

    sound : (x : Nat) → El (code x) → G.Generated x
    sound x (t , root , correct) =
      subst G.Generated root (tree-sound t correct)

    complete : (x : Nat) → G.Generated x → El (code x)
    complete x (G.step mx below) = introduce x mx
      (λ y edge → complete y (below y edge))

    -- The induction target may be a larger class. The caller must supply
    -- the rule premise; membership in this coded generated set is available.
    eliminate : {q : Level} (Q : Nat → Set q)
      → ((x : Nat) → El (code x) → El (M x)
          → ((y : Nat) → El (Pred x y) → Q y) → Q x)
      → (x : Nat) → El (code x) → Q x
    eliminate Q closed x cx = G.induct Q
      (λ y gy my ih → closed y (complete y gy) my ih) x (sound x cx)
