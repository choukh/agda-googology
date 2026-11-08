# 从同一种类见证读取其低层关系

Ω分量的Kind含具体Tree证据，低层关系沿该同一证据读取。坐标与低层
树之间的运输也保留该证据，不比较或替换两份Layer证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedOmegaCodeIf where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (lvl)
open import OCF.Lean.HigherIndexConsumeCode using (from)
open import OCF.Lean.GeneralOmegaEmbedOmegaIf

low : ∀ x κ → E (Lv x) κ → HB (Lv (lvl x κ))
low lz () a
low (ls x) (inj₁ κ) a = low x κ a
low (ls x) (inj₂ _) a = a
low (ll f) (n , κ) a = low (f n) κ a
low (lΩ k g) (inj₁ _ , inj₁ κ) a = low k κ a
low (lΩ k g) (inj₁ _ , inj₂ _) a = a
low (lΩ k g) (inj₂ d , κ) a = low (g d) κ a

lower : ∀ {x y} (p : Layer x y) {κ κ′} → Kind p κ κ′ → Layer (lvl x κ) (lvl y κ′)
lower lz′ {()} r
lower (ls′ p) {inj₁ κ} {inj₁ κ′} r = lower p {κ} {κ′} r
lower (ls′ p) {inj₁ κ} {inj₂ _} ()
lower (ls′ p) {inj₂ _} {inj₁ κ′} ()
lower (ls′ p) {inj₂ _} {inj₂ _} r = p
lower (ll′ p) {(n , κ)} {(.n , κ′)} (refl , r) = lower (p n) {κ} {κ′} r
lower (lo′ p q) {(inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₁ κ′)} r = lower p {κ} {κ′} r
lower (lo′ p q) {(inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₂ _)} ()
lower (lo′ p q) {(inj₁ _ , inj₂ _)} {(inj₁ _ , inj₁ κ′)} ()
lower (lo′ p q) {(inj₁ _ , inj₂ _)} {(inj₁ _ , inj₂ _)} r = p
lower (lo′ p q) {(inj₁ _ , κ)} {(inj₂ b , κ′)} ()
lower (lo′ p q) {(inj₂ a , κ)} {(inj₁ _ , κ′)} ()
lower (lo′ p q) {(inj₂ a , κ)} {(inj₂ b , κ′)} (r , s) = lower (q r) {κ} {κ′} s

decode : ∀ {x y} (p : Layer x y) {κ κ′} (r : Kind p κ κ′) {a b} →
  Coord p r a b → Tree (lower p {κ} {κ′} r) (low x κ a) (low y κ′ b)
decode lz′ {()} r s
decode (ls′ p) {inj₁ κ} {inj₁ κ′} r s = decode p {κ} {κ′} r s
decode (ls′ p) {inj₁ κ} {inj₂ _} () s
decode (ls′ p) {inj₂ _} {inj₁ κ′} () s
decode (ls′ p) {inj₂ _} {inj₂ _} r s = s
decode (ll′ p) {(n , κ)} {(.n , κ′)} (refl , r) s = decode (p n) {κ} {κ′} r s
decode (lo′ p q) {(inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₁ κ′)} r s = decode p {κ} {κ′} r s
decode (lo′ p q) {(inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₂ _)} () s
decode (lo′ p q) {(inj₁ _ , inj₂ _)} {(inj₁ _ , inj₁ κ′)} () s
decode (lo′ p q) {(inj₁ _ , inj₂ _)} {(inj₁ _ , inj₂ _)} r s = s
decode (lo′ p q) {(inj₁ _ , κ)} {(inj₂ b , κ′)} () s
decode (lo′ p q) {(inj₂ a , κ)} {(inj₁ _ , κ′)} () s
decode (lo′ p q) {(inj₂ a , κ)} {(inj₂ b , κ′)} (r , s) t = decode (q r) {κ} {κ′} s t

encode : ∀ {x y} (p : Layer x y) {κ κ′} (r : Kind p κ κ′) {a b} →
  Tree (lower p {κ} {κ′} r) a b → Coord p r (from x κ a) (from y κ′ b)
encode lz′ {()} r s
encode (ls′ p) {inj₁ κ} {inj₁ κ′} r s = encode p {κ} {κ′} r s
encode (ls′ p) {inj₁ κ} {inj₂ _} () s
encode (ls′ p) {inj₂ _} {inj₁ κ′} () s
encode (ls′ p) {inj₂ _} {inj₂ _} r s = s
encode (ll′ p) {(n , κ)} {(.n , κ′)} (refl , r) s = encode (p n) {κ} {κ′} r s
encode (lo′ p q) {(inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₁ κ′)} r s = encode p {κ} {κ′} r s
encode (lo′ p q) {(inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₂ _)} () s
encode (lo′ p q) {(inj₁ _ , inj₂ _)} {(inj₁ _ , inj₁ κ′)} () s
encode (lo′ p q) {(inj₁ _ , inj₂ _)} {(inj₁ _ , inj₂ _)} r s = s
encode (lo′ p q) {(inj₁ _ , κ)} {(inj₂ b , κ′)} () s
encode (lo′ p q) {(inj₂ a , κ)} {(inj₁ _ , κ′)} () s
encode (lo′ p q) {(inj₂ a , κ)} {(inj₂ b , κ′)} (r , s) t = encode (q r) {κ} {κ′} s t
```

decode/encode不是任意两个低层关系之间的运输。lower p r保留同一个p、r，
包括Ω组件里的那份Tree证据；后续实际code保持须在这个返回关系上证明。
