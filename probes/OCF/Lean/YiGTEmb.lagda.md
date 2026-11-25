# 一般目标的嵌入行
验收文件（读记号）；逐条跟随 `YiTBRow.ψ` 的自身、一致、下标层、指定孩子及比较表分支。
孩子只用结构较低源层的保持，更新底的前缀显式传入；自身行调用一般上折定理。
`IndexOK` 排除表缺项的指定孩子路径，本文件不为回退行补一个保持结论。
入口：`emb-row`、`self-child`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTEmb where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (_∷_; []; _++_)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (OK; updated-ok)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiGTGen using (emb-pres)
open import OCF.Lean.YiGTNode using (NodeFrame)
open import OCF.Lean.YiGTIndex
open import OCF.Lean.YiGTUp using (UpFrame; up-pres)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

self-child : ∀ s h (o : Ok (nd s h)) ν → NodeFrame (nd s h) o (nd s h) self ν
  → (c : Ch s) → UpFrame ν (h c) (down {s = s} {h = h} stop c)
self-child s h o ν fr c p κ nu = proj₁ (fr (inj₂ (c , inj₂ p)) κ nu) , nu , λ η z lc → lc

module Top (s : Sh) (h : Ch s → L) (child : (c : Ch s) → PresAt (h c))
  (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h))
  (gb : OK B) (t : E.T) (pref : PrefixU B t) where
  cb : (x : Tr (nd s h)) (c : Ch s) → Base (h c)
  cb x c i u = ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x

  child-at : ∀ j ν {a b x} (c : Ch s) (v : j ≤ h c) → IndexOK (h c) (proj₂ o c) (proj₂ r c) j v ν
    → (β : Tr⁺ j) → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ β) → GR.R (nd s h) a x
    → PrefixU (cb x c) (t ++ a) → (y : Tr (h c)) → GR.R (h c) b y
    → GR.R j (E.ψ ν ((t ++ a) ++ b) ∷ []) (proj₁ (ψ (h c) (proj₂ o c) (proj₂ r c) (cb x c) j v β y))
  child-at j ν {a} {b} {x} c v ic β mb m pc y ch = child c (proj₂ o c) (proj₂ r c) (cb x c)
    (updated-ok s h o r B gb x c) (t ++ a) pc
    j v ν ic β mb ch

emb-row : ∀ s h (child : (c : Ch s) → PresAt (h c))
  → (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (gb : OK B)
  → (t : E.T) (pref : PrefixU B t) → ∀ j (w : j ≤ nd s h) ν → IndexOK (nd s h) o r j w ν
  → (β : Tr⁺ j) → ∀ {a b x} (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → GR.R (nd s h) a x
  → ((d : Ch s) → PrefixU (Top.cb s h child o r B gb t pref x d) (t ++ a))
  → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ (nd s h) o r B j w β x))
  → GR.R (h c) b y
  → GR.R j (E.ψ ν ((t ++ a) ++ b) ∷ []) (proj₁ (ψ (nd s h) o r B j w β (up x c y e)))
emb-row s h child o r B gb t pref .(nd s h) self ν (fr , rt) β {a} c y e m pc mx ch =
  up-pres (h c) ν (down {s = s} {h = h} stop c) (self-child s h o ν fr c) (t ++ a)
    (ψ (nd s h) o r B (nd s h) self β _) mx ch
emb-row s h child o r B gb t pref j (inu ws) ν (fr , rt) β c y e m pc mx ch =
  Top.child-at s h child o r B gb t pref j ν c (ws c) (rt c) _ mx m (pc c) y ch
emb-row (sΩ k) h child o r B gb t pref j (ink v) ν (fr , rt) β c y e m pc mx ch =
  Top.child-at (sΩ k) h child o r B gb t pref j ν c (v ∙ proj₂ (proj₁ o) c) (rt c) _ mx m (pc c) y ch
emb-row sS h child o r B gb t pref j (inc tt v) ν (fr , rt) β tt y e m pc mx ch =
  Top.child-at sS h child o r B gb t pref j ν tt v rt _ mx m (pc tt) y ch
emb-row sL h child o r B gb t pref j (inc n v) ν (fr , rt) β m y e q pc mx ch
  with way h (proj₁ o) m n | rt m
... | inj₁ u | ic = Top.child-at sL h child o r B gb t pref j ν n v ic _ mx q (pc n)
  (proj₁ (emb (h n) (proj₂ o n) u (y , e))) (emb-pres (h n) (proj₂ o n) u (y , e) ch)
... | inj₂ u | ic = Top.child-at sL h child o r B gb t pref j ν m (v ∙ u) ic _ mx q (pc m) y ch
emb-row (sΩ k) h child o r B gb t pref j (inc c′ v) ν (fr , rt) β c y e m pc mx ch
  with proj₁ r c c′ | rt c
... | just (inj₁ u) | ic = Top.child-at (sΩ k) h child o r B gb t pref j ν c (v ∙ u) ic _ mx m (pc c) y ch
... | just (inj₂ u) | ic = Top.child-at (sΩ k) h child o r B gb t pref j ν c′ v ic _ mx m (pc c′)
  (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))) (emb-pres (h c′) (proj₂ o c′) u (y , e) ch)
... | nothing | ()
```
