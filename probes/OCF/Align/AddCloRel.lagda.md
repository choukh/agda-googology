# 换一步: 折叠对输入和状态的单调性

> 不含记号, 不含旧树. 入口 [AddClo](AddClo.lagda.md). 这里只讲 [TLRuleSum](TLRuleSum.lagda.md) 的折叠本身.
>
> `Rel k x y` ($x\trianglelefteq y$): 同一层上两棵和的逻辑关系. 主定理 `main`: 两个字面相连的世界 $W_1\lhd W_2$ 里的两个折叠 (`S₁`, `S₂` 可以不同), 只要原子的作用相关, 输入相关, 状态相关, 输出就相关. **没有证书, 对一切世界, 一步, 不分阶段.** 第 0 层上 `Rel` 给值的 $\le$ (`sum-mono`).
>
> 这和 `Cumsum.ψᴱ-not-mono`, `Certified.ψ-not-⊑mono`, `no-full` 不矛盾: `Rel` 里**没有** "低层的东西 $\trianglelefteq$ 高层节点" 这一条, $5\trianglelefteq\Omega_1$ 推不出来. `ni` 只和同一个分支的 `ni` 比, 坐标按 `Rel` 对应.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddCloRel where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)
open import OCF.BTBO using (injᶜ; module Trich)
open Trich renaming (<-dec to <ᴺ-dec) using ()
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSum using (D; n0; n1; _⨾_; nl; ni; Dif; Ωd; inS; outS; out-inS; sum; pt; sum-fst; AccL; acc; accL; ≪≪; Int; Ipt; module Fold; module Gen; ω⋅)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; ⊲→≤)
```

## §1 关系

每一条都是折叠看得见的形状. `r0`: 空的不大于任何东西. `rf`, `rs`: 接上别的东西不变小, 接在前面或后面都行. `rp`: 极限逐项. `rn`: 不大于某一项就不大于极限. `rt`: 前一段进第 $n$ 项, 后一段进后面的项. `ri`: 同一分支的节点, 坐标相关则被积函数相关 (所以 `Rel x x` 就是 "x 对坐标单调"; 它不是自反的).

```agda
module _ (k : A) (lw : ∀ {j} → j ≪ k → D j → D j → Set) where
  infix 4 R₊
  data R₊ : D k → D k → Set where
    r0 : ∀ {y} → R₊ n0 y
    r1 : R₊ n1 n1
    r⨾ : ∀ {x x′ y y′} → R₊ x x′ → R₊ y y′ → R₊ (x ⨾ y) (x′ ⨾ y′)
    rf : ∀ {x x′ y} → R₊ x x′ → R₊ x (x′ ⨾ y)
    rs : ∀ {x x′ y} → R₊ x y → R₊ x (x′ ⨾ y)
    rp : ∀ {d d′} → (∀ n → R₊ (d n) (d′ n)) → R₊ (nl d) (nl d′)
    rn : ∀ {x d} n → R₊ x (d n) → R₊ x (nl d)
    rt : ∀ {x y d} n → R₊ x (d n) → R₊ y (nl (λ m → d (suc (m + n)))) → R₊ (x ⨾ y) (nl d)
    ri : ∀ {j} {r : j ≪ k} {u u′} →
         (∀ z z′ → lw r z z′ → R₊ (u (inS (≪S r) z)) (u′ (inS (≪S r) z′))) → R₊ (ni r u) (ni r u′)

Rel : ∀ k → D k → D k → Set
Low : ∀ k {j} → j ≪ k → D j → D j → Set
Rel k = R₊ k (Low k)
Low (asuc a) C.zero = Rel a
Low (asuc a) (C.suc r) = Low a r
Low (alim f) (C.lim n r) = Low (f n) r

toR : ∀ {k j} (r : j ≪ k) {x y} → Low k r x y → Rel j x y
toR C.zero p = p
toR (C.suc r) p = toR r p
toR (C.lim n r) p = toR r p

ofR : ∀ {k j} (r : j ≪ k) {x y} → Rel j x y → Low k r x y
ofR C.zero p = p
ofR (C.suc r) p = ofR r p
ofR (C.lim n r) p = ofR r p

-- 极限的项逐项相等就可以换, 不要函数外延
nl-cong : ∀ {k} {lw : ∀ {j} → j ≪ k → D j → D j → Set} {x} {f g : ℕ → D k} → R₊ k lw x (nl f) → (∀ m → f m ≡ g m) → R₊ k lw x (nl g)
nl-cong r0 e = r0
nl-cong {k} {lw} (rp {d} p) e = rp (λ n → subst (R₊ k lw (d n)) (e n) (p n))
nl-cong {k} {lw} {x} (rn n q) e = rn n (subst (R₊ k lw x) (e n) q)
nl-cong {k} {lw} (rt {x = x} n q q′) e = rt n (subst (R₊ k lw x) (e n) q) (nl-cong q′ (λ m → e (suc (m + n))))

-- 输出的节点: 坐标是 outS y
ri-out : ∀ {t j} (s : j ≪ t) {G G′ : D j → D t} → (∀ z z′ → Rel j z z′ → Rel t (G z) (G′ z′)) →
         Rel t (ni s (λ y → G (outS (≪S s) y))) (ni s (λ y → G′ (outS (≪S s) y)))
ri-out {t} s {G} {G′} h = ri (λ z z′ e →
  subst₂ (Rel t) (sym (cong G (out-inS (≪S s) z))) (sym (cong G′ (out-inS (≪S s) z′))) (h z z′ (toR s e)))
```

## §2 坐标的积分

`AccL` 的证明不影响值: 两边可以用不同的证明.

```agda
iptR : ∀ {j k} (ac₁ ac₂ : AccL j) (r : j ≪ k) (u u′ : D j → D k) {w w′ d d′} → Rel j w w′ → (∀ n → Rel j (d n) (d′ n)) → ∀ n → Rel j (Ipt ac₁ r u w d n) (Ipt ac₂ r u′ w′ d′ n)
iptR ac₁ ac₂ r u u′ h p zero = h
iptR ac₁ ac₂ r u u′ h p (suc n) = r⨾ (iptR ac₁ ac₂ r u u′ h p n) (p n)

iptU : ∀ {j k} (ac : AccL j) (r : j ≪ k) (u : D j → D k) {w w′ d} → Rel j w w′ → ∀ n → Rel j w (Ipt ac r u w′ d n)
iptU ac r u h zero = h
iptU ac r u h (suc n) = rf (iptU ac r u h n)

intm : ∀ {j k} (ac₁ ac₂ : AccL j) (r : j ≪ k) {u u′ : D j → D k} → (∀ z z′ → Rel j z z′ → Rel k (u z) (u′ z′)) →
       ∀ {w w′ x x′} → Rel j w w′ → Rel j x x′ → Rel k (Int ac₁ r u w x) (Int ac₂ r u′ w′ x′)
intm ac₁ ac₂ r hu h r0 = r0
intm ac₁ ac₂ r hu h r1 = hu _ _ h
intm ac₁ ac₂ r hu h (r⨾ d e) = r⨾ (intm ac₁ ac₂ r hu h d) (intm ac₁ ac₂ r hu (r⨾ h d) e)
intm ac₁ ac₂ r hu h (rf d) = rf (intm ac₁ ac₂ r hu h d)
intm ac₁ ac₂ r hu h (rs d) = rs (intm ac₁ ac₂ r hu (rf h) d)
intm ac₁ ac₂ r {u} {u′} hu h (rp p) = rp (λ n → intm ac₁ ac₂ r hu (iptR ac₁ ac₂ r u u′ h p n) (p n))
intm ac₁ ac₂ r {u} {u′} hu h (rn n d) = rn n (intm ac₁ ac₂ r hu (iptU ac₂ r u′ h n) d)
intm ac₁ ac₂ r {u} {u′} hu {w} {w′} h (rt {x = x} {y = y} {d = d} n d₁ d₂) =
  rt n (intm ac₁ ac₂ r hu (iptU ac₂ r u′ h n) d₁)
    (nl-cong (intm ac₁ ac₂ r hu (r⨾ (iptU ac₂ r u′ h n) d₁) d₂)
      (λ m → cong (λ a → Int ac₂ r u′ a (d (suc (m + n)))) (eqI m)))
  where
  eqI : ∀ m → Ipt ac₂ r u′ (Ipt ac₂ r u′ w′ d n ⨾ d n) (λ m₁ → d (suc (m₁ + n))) m ≡ Ipt ac₂ r u′ w′ d (suc (m + n))
  eqI zero = refl
  eqI (suc m) = cong (λ a → a ⨾ d (suc (m + n))) (eqI m)
intm (acc f₁) (acc f₂) r hu h (ri {r = r′} q) = ri-out (≪≪ r′ r) (λ z z′ e →
  intm (acc f₁) (acc f₂) r hu (r⨾ h (intm (f₁ r′) (f₂ r′) r′ (λ a b g → q a b (ofR r′ g)) r0 e)) (q z z′ (ofR r′ e)))
```

## §3 $\Omega$ 对自己相关

```agda
reflDif : ∀ b {a L} (p : a ⊲ b) (q : b ⊲ L) (w : Lg b) → Rel L (Dif b p q w) (Dif b p q w)
reflDif b C.self q w = r0
reflDif (asuc c) (C.suc p) q w = r⨾ (reflDif c p (⊲-tr (C.suc C.self) q) w) (ri (λ _ _ _ → r1))
reflDif (alim f) (C.lim n p) q (st , w) =
  r⨾ (reflDif (f n) p (⊲-tr (C.lim n C.self) q) (w n))
     (rp (λ m → reflDif (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) q) (w (suc (m + n)))))

reflΩ : ∀ a {L} (q : a ⊲ L) (w : Lg a) → Rel L (Ωd a q w) (Ωd a q w)
reflΩ a q w = r⨾ r1 (reflDif a (z⊲ a) q w)

oneΩ : ∀ a {L} (q : a ⊲ L) (w : Lg a) {y} → Rel L n1 (Ωd a q w ⨾ y)
oneΩ a q w = rf (rf r1)
```

## §4 比较不随世界变

世界 $W_1\lhd W_2$ 里的两个第一位置, 在 $W_2$ 里比和在 $W_1$ 里比结果相同. 这是定理, 不是约定 (`cmp-tr`). 所以折叠可以跨世界比较, 只要上界字面相连.

```agda
dec-self : ∀ n → <ᴺ-dec n n ≡ injᶜ refl
dec-self zero = refl
dec-self (suc n) rewrite dec-self n = refl

⊲-assoc : ∀ {a b c d} (p : a ⊲ b) (q : b ⊲ c) (s : c ⊲ d) → ⊲-tr (⊲-tr p q) s ≡ ⊲-tr p (⊲-tr q s)
⊲-assoc p q C.self = refl
⊲-assoc p q (C.suc s) = cong C.suc (⊲-assoc p q s)
⊲-assoc p q (C.lim n s) = cong (C.lim n) (⊲-assoc p q s)

≪∘-tr : ∀ {k a b c} (r : k ≪ a) (q : a ⊲ b) (s : b ⊲ c) → ≪∘ r (⊲-tr q s) ≡ ≪∘ (≪∘ r q) s
≪∘-tr r q C.self = refl
≪∘-tr r q (C.suc s) = cong C.suc (≪∘-tr r q s)
≪∘-tr r q (C.lim n s) = cong (C.lim n) (≪∘-tr r q s)

cmp-tr : ∀ {j t V W} (c : V ⊲ W) (r : j ≪ V) (τ : t ⊲ V) (lW : Lg W) → cmpN (≪∘ r c) (⊲-tr τ c) lW ≡ cmpN r τ (lg⊲ c lW)
cmp-tr C.self r τ lW = refl
cmp-tr (C.suc c) r τ lW = cmp-tr c r τ lW
cmp-tr (C.lim n c) r τ (st , w) rewrite dec-self n = cmp-tr c r τ (w n)

lg-tr : ∀ {a b c} (p : a ⊲ b) (q : b ⊲ c) (w : Lg c) → lg⊲ (⊲-tr p q) w ≡ lg⊲ p (lg⊲ q w)
lg-tr p C.self w = refl
lg-tr p (C.suc q) w = lg-tr p q w
lg-tr p (C.lim n q) w = lg-tr p q (proj₂ w n)
```

## §5 主定理

世界 $W_1\lhd W_2$, 两个折叠. `S₁`, `S₂` 只是模块参数; `Run` 的正文不提 `S`, 所以 `A₁`, `A₂` 可以是任何原子. 目标 $\tau$ 在左边是 $\tau$, 在右边是 $\tau$ 接上 $c$. 只有这一个定理, 同一个世界是 $c=$ `self`.

```agda
module Main (W₁ W₂ : A) (c : W₁ ⊲ W₂) (lW₂ : Lg W₂) (S₁ S₂ : ∀ {t} → D t → D t) where
  lW₁ : Lg W₁
  lW₁ = lg⊲ c lW₂

  module F₁ = Fold W₁ lW₁ S₁
  module F₂ = Fold W₂ lW₂ S₂

  St₁ St₂ : Set
  St₁ = ∀ {t} → t ⊲ W₁ → D t
  St₂ = ∀ {t} → t ⊲ W₂ → D t

  RS : St₁ → St₂ → Set
  RS Y Y′ = ∀ {t} (τ : t ⊲ W₁) → Rel t (Y τ) (Y′ (⊲-tr τ c))

  HA : ∀ {k} → (D k → St₁ → St₁) → (D k → St₂ → St₂) → Set
  HA {k} A₁ A₂ = ∀ {w w′} {Y : St₁} {Y′ : St₂} → Rel k w w′ → RS Y Y′ → RS (A₁ w Y) (A₂ w′ Y′)

  rptUw : ∀ {k} ac (kp : k ⊲ W₂) (A₂ : D k → St₂ → St₂) {w w′ d} {Y′ : St₂} → Rel k w w′ → ∀ n → Rel k w (proj₁ (F₂.Rpt ac kp A₂ w′ d Y′ n))
  rptUw ac kp A₂ h zero = h
  rptUw ac kp A₂ h (suc n) = rf (rptUw ac kp A₂ h n)

  rptUY : ∀ {k} ac (kp : k ⊲ W₂) (A₂ : D k → St₂ → St₂) {w′ d} {Y : St₁} {Y′ : St₂} → RS Y Y′ → ∀ n → RS Y (proj₂ (F₂.Rpt ac kp A₂ w′ d Y′ n))
  rptUY ac kp A₂ hY zero τ = hY τ
  rptUY ac kp A₂ hY (suc n) τ = rf (rptUY ac kp A₂ hY n τ)

  sq↓ : ∀ {j k} (r : j ≪ k) {kp₁ : k ⊲ W₁} {kp₂ : k ⊲ W₂} → ⊲-tr kp₁ c ≡ kp₂ → ⊲-tr (⊲-tr (≪⊲ r) kp₁) c ≡ ⊲-tr (≪⊲ r) kp₂
  sq↓ r {kp₁} refl = ⊲-assoc (≪⊲ r) kp₁ c

  cmp≡ : ∀ {j k t} (r : j ≪ k) {kp₁ : k ⊲ W₁} {kp₂ : k ⊲ W₂} → ⊲-tr kp₁ c ≡ kp₂ → (τ : t ⊲ W₁) →
         cmpN (≪∘ r kp₂) (⊲-tr τ c) lW₂ ≡ cmpN (≪∘ r kp₁) τ lW₁
  cmp≡ r {kp₁} refl τ = trans (cong (λ a → cmpN a (⊲-tr τ c) lW₂) (≪∘-tr r kp₁ c)) (cmp-tr c (≪∘ r kp₁) τ lW₂)

  main : ∀ {k} (ac₁ ac₂ : AccL k) (kp₁ : k ⊲ W₁) (kp₂ : k ⊲ W₂) (sq : ⊲-tr kp₁ c ≡ kp₂) (A₁ : D k → St₁ → St₁) (A₂ : D k → St₂ → St₂) (hA : HA A₁ A₂)
         {w w′ x x′} {Y : St₁} {Y′ : St₂} → Rel k w w′ → Rel k x x′ → RS Y Y′ → RS (F₁.Run ac₁ kp₁ A₁ w x Y) (F₂.Run ac₂ kp₂ A₂ w′ x′ Y′)

  rptR : ∀ {k} (ac₁ ac₂ : AccL k) (kp₁ : k ⊲ W₁) (kp₂ : k ⊲ W₂) (sq : ⊲-tr kp₁ c ≡ kp₂) (A₁ : D k → St₁ → St₁) (A₂ : D k → St₂ → St₂) (hA : HA A₁ A₂)
         {w w′ d d′} {Y : St₁} {Y′ : St₂} → Rel k w w′ → (∀ n → Rel k (d n) (d′ n)) → RS Y Y′ →
         ∀ n → Rel k (proj₁ (F₁.Rpt ac₁ kp₁ A₁ w d Y n)) (proj₁ (F₂.Rpt ac₂ kp₂ A₂ w′ d′ Y′ n)) × RS (proj₂ (F₁.Rpt ac₁ kp₁ A₁ w d Y n)) (proj₂ (F₂.Rpt ac₂ kp₂ A₂ w′ d′ Y′ n))

  chnR : ∀ {j} (ac₁ ac₂ : AccL j) (ρ₁ : j ⊲ W₁) (ρ₂ : j ⊲ W₂) (sq : ⊲-tr ρ₁ c ≡ ρ₂) (A₁ : D j → St₁ → St₁) (A₂ : D j → St₂ → St₂) (hA : HA A₁ A₂)
         {Y : St₁} {Y′ : St₂} → RS Y Y′ →
         ∀ n → Rel j (proj₁ (F₁.Chn ac₁ ρ₁ A₁ Y n)) (proj₁ (F₂.Chn ac₂ ρ₂ A₂ Y′ n))
             × Rel j (proj₁ (proj₂ (F₁.Chn ac₁ ρ₁ A₁ Y n))) (proj₁ (proj₂ (F₂.Chn ac₂ ρ₂ A₂ Y′ n)))
             × RS (proj₂ (proj₂ (F₁.Chn ac₁ ρ₁ A₁ Y n))) (proj₂ (proj₂ (F₂.Chn ac₂ ρ₂ A₂ Y′ n)))

  mainK : ∀ {j k t} (ac₁ ac₂ : AccL k) (ac₁′ ac₂′ : AccL j) (r : j ≪ k) (kp₁ : k ⊲ W₁) (kp₂ : k ⊲ W₂) (sq : ⊲-tr kp₁ c ≡ kp₂) (A₁ : D k → St₁ → St₁) (A₂ : D k → St₂ → St₂) (hA : HA A₁ A₂)
          {u u′} → (∀ z z′ → Low k r z z′ → Rel k (u (inS (≪S r) z)) (u′ (inS (≪S r) z′))) →
          ∀ {w w′} {Y : St₁} {Y′ : St₂} → Rel k w w′ → RS Y Y′ → (τ : t ⊲ W₁) (c₀ : Rk j t) →
          Rel t (F₁.RunK ac₁ ac₁′ kp₁ A₁ w r u Y τ c₀) (F₂.RunK ac₂ ac₂′ kp₂ A₂ w′ r u′ Y′ (⊲-tr τ c) c₀)

  main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h r0 hY τ = r0
  main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h r1 hY τ = hA h hY τ
  main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h (r⨾ d e) hY τ =
    r⨾ (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h d hY τ)
       (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (r⨾ h d) e (λ τ′ → r⨾ (hY τ′) (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h d hY τ′)) τ)
  main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h (rf d) hY τ = rf (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h d hY τ)
  main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h (rs d) hY τ = rs (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (rf h) d (λ τ′ → rf (hY τ′)) τ)
  main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h (rp p) hY τ =
    rp (λ n → main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (proj₁ (rptR ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h p hY n)) (p n) (proj₂ (rptR ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h p hY n)) τ)
  main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h (rn n d) hY τ =
    rn n (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (rptUw ac₂ kp₂ A₂ h n) d (rptUY ac₂ kp₂ A₂ hY n) τ)
  main {k} ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA {w} {w′} {Y = Y} {Y′} h (rt {x = x} {d = d} n d₁ d₂) hY {t} τ =
    rt n (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (rptUw ac₂ kp₂ A₂ h n) d₁ (rptUY ac₂ kp₂ A₂ hY n) τ)
      (nl-cong
        (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (r⨾ (rptUw ac₂ kp₂ A₂ h n) d₁) d₂
          (λ τ′ → r⨾ (rptUY ac₂ kp₂ A₂ hY n τ′) (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (rptUw ac₂ kp₂ A₂ h n) d₁ (rptUY ac₂ kp₂ A₂ hY n) τ′)) τ)
        (λ m → cong (λ (p : D k × St₂) → F₂.Run ac₂ kp₂ A₂ (proj₁ p) (d (suc (m + n))) (proj₂ p) (⊲-tr τ c)) (eqR m)))
    where
    R₀ = F₂.Rpt ac₂ kp₂ A₂ w′ d Y′
    eqR : ∀ m → F₂.Rpt ac₂ kp₂ A₂ (proj₁ (R₀ (suc n))) (λ m₁ → d (suc (m₁ + n))) (proj₂ (R₀ (suc n))) m ≡ R₀ (suc (m + n))
    eqR zero = refl
    eqR (suc m) = cong (λ (p : D k × St₂) → (proj₁ p ⨾ d (suc (m + n))) , (λ {t₂} τ₂ → proj₂ p τ₂ ⨾ F₂.Run ac₂ kp₂ A₂ (proj₁ p) (d (suc (m + n))) (proj₂ p) τ₂)) (eqR m)
  main {k} (acc f₁) (acc f₂) kp₁ kp₂ sq A₁ A₂ hA {w} {w′} {Y = Y} {Y′} h (ri {j} {r = r} {u} {u′} q) hY {t} τ =
    subst (λ c₀ → Rel t (F₁.RunK (acc f₁) (f₁ r) kp₁ A₁ w r u Y τ (cmpN (≪∘ r kp₁) τ lW₁)) (F₂.RunK (acc f₂) (f₂ r) kp₂ A₂ w′ r u′ Y′ (⊲-tr τ c) c₀))
      (sym (cmp≡ r sq τ))
      (mainK (acc f₁) (acc f₂) (f₁ r) (f₂ r) r kp₁ kp₂ sq A₁ A₂ hA q h hY τ (cmpN (≪∘ r kp₁) τ lW₁))

  rptR ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h p hY zero = h , hY
  rptR ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h p hY (suc n) =
    r⨾ (proj₁ (rptR ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h p hY n)) (p n) ,
    λ τ → r⨾ (proj₂ (rptR ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h p hY n) τ)
             (main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (proj₁ (rptR ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h p hY n)) (p n) (proj₂ (rptR ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA h p hY n)) τ)

  chnR {j} ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA {Y} {Y′} hY zero = r0 , (subst (λ a → Rel j (Y ρ₁) (Y′ a)) sq (hY ρ₁) , hY)
  chnR {j} ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY (suc n) =
    r⨾ (proj₁ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n)) (proj₁ (proj₂ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n))) ,
    (subst (λ a → Rel j _ (F₂.Run ac₂ ρ₂ A₂ _ _ _ a)) sq
       (main ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA (proj₁ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n)) (proj₁ (proj₂ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n))) (proj₂ (proj₂ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n))) ρ₁) ,
     λ τ → r⨾ (proj₂ (proj₂ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n)) τ)
              (main ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA (proj₁ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n)) (proj₁ (proj₂ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n))) (proj₂ (proj₂ (chnR ac₁ ac₂ ρ₁ ρ₂ sq A₁ A₂ hA hY n))) τ))

  mainK {j} {k} ac₁ ac₂ ac₁′ ac₂′ r kp₁ kp₂ sq A₁ A₂ hA {u} {u′} q {w} {w′} {Y} {Y′} h hY τ (keep s) = ri-out s (λ z z′ e →
    main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA
      {Y = Y F₁.⊕ F₁.Run ac₁′ (⊲-tr (≪⊲ r) kp₁) (F₁.Ai ac₁ r kp₁ ac₁′ A₁ w u) n0 z Y}
      {Y′ = Y′ F₂.⊕ F₂.Run ac₂′ (⊲-tr (≪⊲ r) kp₂) (F₂.Ai ac₂ r kp₂ ac₂′ A₂ w′ u′) n0 z′ Y′}
      (r⨾ h (intm ac₁′ ac₂′ r (λ a b g → q a b (ofR r g)) r0 e))
      (q z z′ (ofR r e))
      (λ τ′ → r⨾ (hY τ′)
        (main ac₁′ ac₂′ (⊲-tr (≪⊲ r) kp₁) (⊲-tr (≪⊲ r) kp₂) (sq↓ r sq) (F₁.Ai ac₁ r kp₁ ac₁′ A₁ w u) (F₂.Ai ac₂ r kp₂ ac₂′ A₂ w′ u′)
          (λ {a} {b} g hY′ τ″ → main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (r⨾ h (intm ac₁′ ac₂′ r (λ a′ b′ g′ → q a′ b′ (ofR r g′)) r0 g)) (q a b (ofR r g)) hY′ τ″)
          {Y = Y} {Y′ = Y′} r0 e hY τ′))
      τ)
  mainK {j} {k} ac₁ ac₂ ac₁′ ac₂′ r kp₁ kp₂ sq A₁ A₂ hA {u} {u′} q {w} {w′} {Y} {Y′} h hY τ (rise _) = rp (λ n →
    main ac₁′ ac₂′ ρ₁ ρ₂ (sq↓ r sq) A₁′ A₂′ hA′
      (proj₁ (chnR ac₁′ ac₂′ ρ₁ ρ₂ (sq↓ r sq) A₁′ A₂′ hA′ hY n))
      (proj₁ (proj₂ (chnR ac₁′ ac₂′ ρ₁ ρ₂ (sq↓ r sq) A₁′ A₂′ hA′ hY n)))
      (proj₂ (proj₂ (chnR ac₁′ ac₂′ ρ₁ ρ₂ (sq↓ r sq) A₁′ A₂′ hA′ hY n))) τ)
    where
    ρ₁ = ⊲-tr (≪⊲ r) kp₁
    ρ₂ = ⊲-tr (≪⊲ r) kp₂
    A₁′ = F₁.Ai ac₁ r kp₁ ac₁′ A₁ w u
    A₂′ = F₂.Ai ac₂ r kp₂ ac₂′ A₂ w′ u′
    hA′ : ∀ {a b} {Z : St₁} {Z′ : St₂} → Rel j a b → RS Z Z′ → RS (A₁′ a Z) (A₂′ b Z′)
    hA′ {a} {b} g hZ τ″ = main ac₁ ac₂ kp₁ kp₂ sq A₁ A₂ hA (r⨾ h (intm ac₁′ ac₂′ r (λ a′ b′ g′ → q a′ b′ (ofR r g′)) r0 g)) (q a b (ofR r g)) hZ τ″
```

## §6 第 0 层: 关系给值

```agda
sum-mono : ∀ {b b′ x x′} → b ≤ b′ → Rel azero x x′ → sum b x ≤ sum b′ x′
sum-mono {b′ = b′} {x′ = y} h r0 = ≤-trans h (⊲→≤ (sum-fst b′ y))
sum-mono h r1 = s≤ h
sum-mono {b} {b′} h (r⨾ {x} {x′} d e) = sum-mono {sum b x} {sum b′ x′} (sum-mono h d) e
sum-mono {b′ = b′} h (rf {x′ = x′} {y = y} d) = ≤-trans (sum-mono h d) (⊲→≤ (sum-fst (sum b′ x′) y))
sum-mono {b} {b′} h (rs {x′ = x′} d) = sum-mono {b} {sum b′ x′} (≤-trans h (⊲→≤ (sum-fst b′ x′))) d
sum-mono {b} {b′} h (rp {d} {d′} p) = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b d n ≤ pt b′ d′ n
  go zero = h
  go (suc n) = sum-mono {pt b d n} {pt b′ d′ n} (go n) (p n)
sum-mono {b} {b′} {x} h (rn {d = d} n e) = ≤l (suc n) (sum-mono {b} {pt b′ d n} (go n) e)
  where
  go : ∀ m → b ≤ pt b′ d m
  go zero = h
  go (suc m) = ≤-trans (go m) (⊲→≤ (sum-fst (pt b′ d m) (d m)))
sum-mono {b} {b′} {x₀ ⨾ y₀} h (rt {d = d} n e e′) =
  ≤-trans (sum-mono {sum b x₀} {pt b′ d (suc n)} (sum-mono {b} {pt b′ d n} (go n) e) e′)
          (l≤ (λ m → ≤l (suc (m + n)) (subst (λ a → pt (pt b′ d (suc n)) (λ m₁ → d (suc (m₁ + n))) m ≤ a) (eqP m) (≤-refl _))))
  where
  go : ∀ m → b ≤ pt b′ d m
  go zero = h
  go (suc m) = ≤-trans (go m) (⊲→≤ (sum-fst (pt b′ d m) (d m)))
  eqP : ∀ m → pt (pt b′ d (suc n)) (λ m₁ → d (suc (m₁ + n))) m ≡ pt b′ d (suc (m + n))
  eqP zero = refl
  eqP (suc m) = cong (λ a → sum a (d (suc (m + n)))) (eqP m)
sum-mono h (ri {r = ()} q)
```

## §7 同一个世界, 换一步

`hS`: 一步的比较. 输入都是 $\Omega_t+Y_t$, 所以 $1$ 总在第一位置 (`Rel t n1 c`), $S=+1$ 也写得下.

```agda
SubS : (∀ {t} → D t → D t) → (∀ {t} → D t → D t) → Set
SubS S₁ S₂ = ∀ {t} {c c′ : D t} → Rel t n1 c → Rel t n1 c′ → Rel t c c′ → Rel t (S₁ c) (S₂ c′)

module Step (S₁ S₂ : ∀ {t} → D t → D t) (hS : SubS S₁ S₂) where
  module G₁ = Gen S₁
  module G₂ = Gen S₂

  module _ (y : A) (w : Lg y) where
    open Main y y C.self w S₁ S₂

    hStep : ∀ {k} {a b : D k} {Y : St₁} {Y′ : St₂} → Rel k a b → RS Y Y′ → RS (F₁.Step Y) (F₂.Step Y′)
    hStep _ hY {t} τ = hS (oneΩ t C.self (lg⊲ τ w)) (oneΩ t C.self (lg⊲ τ w)) (r⨾ (reflΩ t C.self (lg⊲ τ w)) (hY τ))

    Rd : ∀ {k} (kp : k ⊲ y) {x x′} → Rel k x x′ → {Y : St₁} {Y′ : St₂} → RS Y Y′ → RS (F₁.Act kp x Y) (F₂.Act kp x′ Y′)
    Rd {k} kp d hY = main (accL k) (accL k) kp kp refl (λ _ Z → F₁.Step Z) (λ _ Z → F₂.Step Z) (hStep {k}) r0 d hY

    Rψ : Rel azero (G₁.Ψd y w) (G₂.Ψd y w)
    Rψ = Rd C.self (reflΩ y C.self w) (λ τ → r0) (z⊲ y)

  Ψ≤ : ∀ y w → G₁.Ψ y w ≤ G₂.Ψ y w
  Ψ≤ y w = sum-mono z≤ (r⨾ r1 (Rψ y w))
```
