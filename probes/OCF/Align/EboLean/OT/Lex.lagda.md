# 和的字典序：前缀、拼接、+1

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.Lex` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

`lt` 在和上是分量表的字典序（[`lt-list`](OrderProps.lagda.md)）。本文件把 (≺′1)(≺′2) 的后果做成引理：
真前缀更小、公共前缀可消、单主元项对和的比较看首分量、`b ≺ d ≺ b + c` 蕴涵 `d = b + d′`、`x + 1 = x ▹ 1` 与 `x ≺ x + 1 ⪯ …`。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.Lex where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Arith using (app; dropLt; _+_)
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OrderProps using (ltLx; lt-list)
open import OCF.Align.EboLean.OT.Unfold
open import OCF.Align.EboLean.OT.Linear
open import OCF.Align.EboLean.OT.Trans

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
```

## 1. toList 与拼接

```agda
toListAcc-++ : ∀ s acc → toListAcc s acc ≡ toList s ++ acc
toListAcc-++ zer     acc = refl
toListAcc-++ (a ▹ p) acc =
  trans (toListAcc-++ a (p ∷ acc))
        (trans (cong (_++ (p ∷ acc)) (sym (++-identityʳ (toList a))))
               (trans (++-assoc (toList a) [] (p ∷ acc)) (sym (trans (cong (_++ acc) (toListAcc-++ a (p ∷ []))) (++-assoc (toList a) (p ∷ []) acc)))))

toList-▹ : ∀ a p → toList (a ▹ p) ≡ toList a ++ (p ∷ [])
toList-▹ a p = toListAcc-++ a (p ∷ [])

toList-app : ∀ a b → toList (app a b) ≡ toList a ++ toList b
toList-app a zer     = sym (++-identityʳ (toList a))
toList-app a (b ▹ q) =
  trans (toList-▹ (app a b) q)
        (trans (cong (_++ (q ∷ [])) (toList-app a b))
               (trans (++-assoc (toList a) (toList b) (q ∷ [])) (cong (toList a ++_) (sym (toList-▹ b q)))))

-- goL（Linear）与 fromList
toList-goL : ∀ a xs → toList (goL a xs) ≡ toList a ++ xs
toList-goL a []       = sym (++-identityʳ (toList a))
toList-goL a (p ∷ ps) = trans (toList-goL (a ▹ p) ps) (trans (cong (_++ ps) (toList-▹ a p)) (++-assoc (toList a) (p ∷ []) ps))

fromL : List PTm → Tm
fromL = goL zer

toList-fromL : ∀ xs → toList (fromL xs) ≡ xs
toList-fromL xs = toList-goL zer xs

fromL-NZ : ∀ p ps → NZ (fromL (p ∷ ps))
fromL-NZ p ps = nz (zer ▹ p) ps tt
  where
    nz : ∀ a xs → NZ a → NZ (goL a xs)
    nz a []       h = h
    nz a (q ∷ qs) h = nz (a ▹ q) qs tt
```

## 2. 表上的字典序引理

```agda
ltLx-nil : ∀ ps → ltLx ps [] ≡ false
ltLx-nil []       = refl
ltLx-nil (p ∷ ps) = refl

++-nonempty : ∀ {A : Set} (zs : List A) z → zs ++ z ∷ [] ≡ [] → ⊥
++-nonempty []       z ()
++-nonempty (x ∷ zs) z ()

ltLx-prefix : ∀ ps qs → (qs ≡ [] → ⊥) → ltLx ps (ps ++ qs) ≡ true
ltLx-prefix ps       []       ne = ⊥-elim (ne refl)
ltLx-prefix []       (q ∷ qs) ne = refl
ltLx-prefix (p ∷ ps) (q ∷ qs) ne = trans (if-true (eqP-refl p)) (ltLx-prefix ps (q ∷ qs) ne)


ltLx-sing : ∀ p ps q → ltLx (p ∷ ps) (q ∷ []) ≡ true → lt ⟨ p ⟩ ⟨ q ⟩ ≡ true
ltLx-sing p ps q h with caseEq (eqP p q)
... | inj₁ e = ⊥-elim (true≢false (trans (sym (trans (sym (if-true e)) h)) (ltLx-nil ps)))
... | inj₂ e = trans (sym (if-false e)) h

≺⇒eqP-false : ∀ p q → lt ⟨ p ⟩ ⟨ q ⟩ ≡ true → eqP p q ≡ false
≺⇒eqP-false p q h with caseEq (eqP p q)
... | inj₂ e = e
... | inj₁ e with eqP-sound p q e
...   | refl = ⊥-elim (true≢false (trans (sym h) (lt-irrefl ⟨ p ⟩)))

ltLx-sing⁻ : ∀ p ps q qs → lt ⟨ p ⟩ ⟨ q ⟩ ≡ true → ltLx (p ∷ ps) (q ∷ qs) ≡ true
ltLx-sing⁻ p ps q qs h = trans (if-false (≺⇒eqP-false p q h)) h
```

## 3. 项上的读出

```agda
leˡ : ∀ s t → lt s t ≡ true → le s t ≡ true
leˡ s t h = ∨ˡ (lt s t) (eqT s t) h

leʳ : ∀ s t → eqT s t ≡ true → le s t ≡ true
leʳ s t h = ∨ʳ (lt s t) (eqT s t) h

lt-zero : ∀ x → lt x zer ≡ false
lt-zero x = trans (lt-list x zer) (ltLx-nil (toList x))

lt-zer : ∀ a p → lt zer (a ▹ p) ≡ true
lt-zer a p = trans (lt-list zer (a ▹ p)) (subst (λ l → ltLx [] l ≡ true) (sym (toList-▹ a p)) (ne (toList a)))
  where
    ne : ∀ zs → ltLx [] (zs ++ p ∷ []) ≡ true
    ne []       = refl
    ne (x ∷ zs) = refl

0⪯′ : ∀ x → le zer x ≡ true
0⪯′ zer     = refl
0⪯′ (a ▹ p) = leˡ zer (a ▹ p) (lt-zer a p)

-- 真前缀严格更小
≺-prefix : ∀ y z → NZ z → lt y (app y z) ≡ true
≺-prefix y (z ▹ q) _ =
  trans (lt-list y (app y (z ▹ q)))
        (trans (cong (ltLx (toList y)) (toList-app y (z ▹ q)))
               (ltLx-prefix (toList y) (toList (z ▹ q)) (λ e → ++-nonempty (toList z) q (trans (sym (toList-▹ z q)) e))))

≺-▹ : ∀ y p → lt y (y ▹ p) ≡ true
≺-▹ y p = ≺-prefix y (zer ▹ p) tt

-- 公共前缀可消

btw : ∀ bs ds cs → ltLx bs ds ≡ true → ltLx ds (bs ++ cs) ≡ true
    → ∃ λ ds′ → (ds ≡ bs ++ ds′) × (ds′ ≡ [] → ⊥) × ltLx ds′ cs ≡ true
btw []       []       cs () _
btw []       (d ∷ ds) cs _  h₂ = (d ∷ ds) , refl , (λ ()) , h₂
btw (b ∷ bs) []       cs () _
btw (b ∷ bs) (d ∷ ds) cs h₁ h₂ with caseEq (eqP b d)
... | inj₁ e with eqP-sound b d e
...   | refl with btw bs ds cs (trans (sym (if-true e)) h₁) (trans (sym (if-true e)) h₂)
...     | ds′ , eq , ne , l = ds′ , cong (b ∷_) eq , ne , l
btw (b ∷ bs) (d ∷ ds) cs h₁ h₂ | inj₂ e =
  ⊥-elim (true≢false (trans (sym (trans (sym (if-false (eqP-false-sym b d e))) h₂))
                             (lt-asym ⟨ b ⟩ ⟨ d ⟩ (trans (sym (if-false e)) h₁))))

fromL-NZ′ : ∀ xs → (xs ≡ [] → ⊥) → NZ (fromL xs)
fromL-NZ′ []       ne = ⊥-elim (ne refl)
fromL-NZ′ (q ∷ qs) ne = fromL-NZ q qs

between-app′ : ∀ b c d → lt b d ≡ true → lt d (app b c) ≡ true
             → ∃ λ d′ → (d ≡ app b d′) × NZ d′ × lt d′ c ≡ true
between-app′ b c d h₁ h₂
  with btw (toList b) (toList d) (toList c) (trans (sym (lt-list b d)) h₁)
           (trans (sym (trans (lt-list d (app b c)) (cong (ltLx (toList d)) (toList-app b c)))) h₂)
... | ds′ , eq , ne , l =
  fromL ds′ , d≡ , fromL-NZ′ ds′ ne ,
  trans (lt-list (fromL ds′) c) (trans (cong (λ l′ → ltLx l′ (toList c)) (toList-fromL ds′)) l)
  where
    d≡ : d ≡ app b (fromL ds′)
    d≡ = toList-inj d (app b (fromL ds′))
           (trans eq (sym (trans (toList-app b (fromL ds′)) (cong (toList b ++_) (toList-fromL ds′)))))
```

## 4. 1 与 +1

`1 = φ′_0 0` 是最小的非零项；`x + 1 = x ▹ 1`（没有分量 ≺ 1，所以 `dropLt` 不删）。

```agda
lt-P-one : ∀ p → lt ⟨ p ⟩ one ≡ false
lt-P-one p with caseEq (eqP p (phi zer zer))
... | inj₁ e = trans (lt-unfold p (phi zer zer)) (if-true e)
... | inj₂ e = trans (lt-unfold≠ p (phi zer zer) e) (body p e)
  where
    body : ∀ p → eqP p (phi zer zer) ≡ false → ltP′ p (phi zer zer) ≡ false
    body (phi a b) _ = sh {bO = lt b ⟨ phi zer zer ⟩} {ea = eqT a zer} {za = lt zer a} (lt-zero a) (lt-zero b) (lt-zero ⟨ phi a b ⟩)
      where
        sh : ∀ {az bz Xz bO ea za : Bool} → az ≡ false → bz ≡ false → Xz ≡ false
           → (az ∧ bO) ∨ (ea ∧ bz) ∨ (za ∧ (Xz ∨ false)) ≡ false
        sh {ea = ea} {za = za} refl refl refl = cong₂ _∨_ (∧-zeroʳ ea) (∧-zeroʳ za)
    body (psi π b) _ = cong not (cong₂ _∧_ (lt-zer zer (psi π b)) (lt-zer zer (psi π b)))
    body (Om a)    _ = cong not (cong₂ _∧_ (lt-zer zer (Om a)) (lt-zer zer (Om a)))
    body I         _ = cong not (cong₂ _∧_ (lt-zer zer I) (lt-zer zer I))

one≺P : ∀ p → eqP (phi zer zer) p ≡ false → lt one ⟨ p ⟩ ≡ true
one≺P p e = trans (lt-lin one ⟨ p ⟩ e) (cong not (lt-P-one p))

one⪯P′ : ∀ p → le one ⟨ p ⟩ ≡ true
one⪯P′ p with caseEq (eqP (phi zer zer) p)
... | inj₁ e = leʳ one ⟨ p ⟩ e
... | inj₂ e = leˡ one ⟨ p ⟩ (one≺P p e)

dropLt-one : ∀ x → dropLt x (phi zer zer) ≡ x
dropLt-one zer     = refl
dropLt-one (a ▹ p) = if-false (lt-P-one p)

+one : ∀ x → x + one ≡ x ▹ phi zer zer
+one x = cong (_▹ phi zer zer) (dropLt-one x)


lex1 : ∀ bs cs → ltLx bs cs ≡ true → (ltLx (bs ++ phi zer zer ∷ []) cs ≡ true) ⊎ (bs ++ phi zer zer ∷ [] ≡ cs)
lex1 []       []       ()
lex1 []       (c ∷ cs) _ with caseEq (eqP (phi zer zer) c)
... | inj₂ e = inj₁ (trans (if-false e) (one≺P c e))
... | inj₁ e with eqP-sound (phi zer zer) c e
lex1 []       (c ∷ [])      _ | inj₁ e | refl = inj₂ refl
lex1 []       (c ∷ c′ ∷ cs) _ | inj₁ e | refl = inj₁ (if-true {b = eqP (phi zer zer) (phi zer zer)} {x = true} {y = lt one one} e)
lex1 (b ∷ bs) []       ()
lex1 (b ∷ bs) (c ∷ cs) h with caseEq (eqP b c)
... | inj₂ e = inj₁ (trans (if-false e) (trans (sym (if-false e)) h))
... | inj₁ e with eqP-sound b c e
...   | refl with lex1 bs cs (trans (sym (if-true e)) h)
...     | inj₁ l  = inj₁ (trans (if-true e) l)
...     | inj₂ eq = inj₂ (cong (b ∷_) eq)

+1-least′ : ∀ b c → lt b c ≡ true → le (b + one) c ≡ true
+1-least′ b c h with lex1 (toList b) (toList c) (trans (sym (lt-list b c)) h)
... | inj₁ l  = leˡ (b + one) c (trans (lt-list (b + one) c) (trans (cong (λ l′ → ltLx l′ (toList c)) tl) l))
  where
    tl : toList (b + one) ≡ toList b ++ phi zer zer ∷ []
    tl = trans (cong toList (+one b)) (toList-▹ b (phi zer zer))
... | inj₂ eq = leʳ (b + one) c (eqT-complete (toList-inj (b + one) c (trans (trans (cong toList (+one b)) (toList-▹ b (phi zer zer))) eq)))


lex1⁻ : ∀ cs xs → ltLx cs (xs ++ phi zer zer ∷ []) ≡ true → (ltLx cs xs ≡ true) ⊎ (cs ≡ xs)
lex1⁻ []       []       _ = inj₂ refl
lex1⁻ []       (x ∷ xs) _ = inj₁ refl
lex1⁻ (c ∷ cs) []       h with caseEq (eqP c (phi zer zer))
... | inj₁ e = ⊥-elim (true≢false (trans (sym (trans (sym (if-true e)) h)) (ltLx-nil cs)))
... | inj₂ e = ⊥-elim (true≢false (trans (sym (trans (sym (if-false e)) h)) (lt-P-one c)))
lex1⁻ (c ∷ cs) (x ∷ xs) h with caseEq (eqP c x)
... | inj₂ e = inj₁ (trans (if-false e) (trans (sym (if-false e)) h))
... | inj₁ e with eqP-sound c x e
...   | refl with lex1⁻ cs xs (trans (sym (if-true e)) h)
...     | inj₁ l  = inj₁ (trans (if-true e) l)
...     | inj₂ eq = inj₂ (cong (c ∷_) eq)

≺+1⇒⪯ : ∀ c x → lt c (x + one) ≡ true → le c x ≡ true
≺+1⇒⪯ c x h with lex1⁻ (toList c) (toList x) (trans (sym (trans (lt-list c (x + one)) (cong (ltLx (toList c)) (trans (cong toList (+one x)) (toList-▹ x (phi zer zer)))))) h)
... | inj₁ l  = leˡ c x (trans (lt-list c x) l)
... | inj₂ eq = leʳ c x (eqT-complete (toList-inj c x eq))
```

## 5. 单主元项对和

```agda
-- s ≠ 0，s ≺ ⟨ k ⟩ ⟹ s ▹ p ≺ ⟨ k ⟩（首分量严格小于 k）
≺-sing-▹ : ∀ s p k → NZ s → lt s ⟨ k ⟩ ≡ true → lt (s ▹ p) ⟨ k ⟩ ≡ true
≺-sing-▹ (a ▹ q) p k _ h =
  trans (lt-list (a ▹ q ▹ p) ⟨ k ⟩)
        (subst (λ l → ltLx l (k ∷ []) ≡ true) (sym (toList-▹ (a ▹ q) p))
               (go (toList (a ▹ q)) refl (trans (sym (lt-list (a ▹ q) ⟨ k ⟩)) h)))
  where
    go : ∀ hs → toList (a ▹ q) ≡ hs → ltLx hs (k ∷ []) ≡ true → ltLx (hs ++ p ∷ []) (k ∷ []) ≡ true
    go []       eq _ = ⊥-elim (++-nonempty (toList a) q (trans (sym (toList-▹ a q)) eq))
    go (h ∷ hs) _  l = ltLx-sing⁻ h (hs ++ p ∷ []) k [] (ltLx-sing h hs k l)

-- ⟨ k ⟩ ≺ s ▹ p ⟹ ⟨ k ⟩ ⪯ s（s ≠ 0）
sing-≺-▹ : ∀ k s p → NZ s → lt ⟨ k ⟩ (s ▹ p) ≡ true → le ⟨ k ⟩ s ≡ true
sing-≺-▹ k (a ▹ q) p _ h =
  go (toList (a ▹ q)) refl
     (trans (sym (trans (lt-list ⟨ k ⟩ (a ▹ q ▹ p)) (cong (ltLx (k ∷ [])) (toList-▹ (a ▹ q) p)))) h)
  where
    go : ∀ hs → toList (a ▹ q) ≡ hs → ltLx (k ∷ []) (hs ++ p ∷ []) ≡ true → le ⟨ k ⟩ (a ▹ q) ≡ true
    go []       eq _ = ⊥-elim (++-nonempty (toList a) q (trans (sym (toList-▹ a q)) eq))
    go (h ∷ hs) eq l with caseEq (eqP k h)
    ... | inj₂ e = leˡ ⟨ k ⟩ (a ▹ q) (trans (lt-list ⟨ k ⟩ (a ▹ q))
                     (subst (λ z → ltLx (k ∷ []) z ≡ true) (sym eq) (ltLx-sing⁻ k [] h hs (trans (sym (if-false e)) l))))
    ... | inj₁ e with eqP-sound k h e
    go (h ∷ [])       eq l | inj₁ e | refl = leʳ ⟨ k ⟩ (a ▹ q) (eqT-complete (toList-inj ⟨ k ⟩ (a ▹ q) (sym eq)))
    go (h ∷ h′ ∷ hs′) eq l | inj₁ e | refl =
      leˡ ⟨ k ⟩ (a ▹ q) (trans (lt-list ⟨ k ⟩ (a ▹ q)) (subst (λ z → ltLx (k ∷ []) z ≡ true) (sym eq) (if-true e)))
```
