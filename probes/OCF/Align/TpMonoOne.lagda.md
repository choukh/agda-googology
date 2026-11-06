# `T⁺` 对输入单调 (六): 第一站 $T^+(0) < T^+(1)$

> 不含记号. 接口 [TpMonoIf](TpMonoIf.lagda.md). [TpMonoHs](TpMonoHs.lagda.md) 把 `Steps.s-hs` 在 $h$ 处归结为 `ChangeHs h` (跨实例) 与 `MonoStepHs h` (实例之内). 本文在 $h=0$ 处把两条都证出来, 于是:
>
> - **`T⁺0<T⁺1 : asuc (T⁺ hz tt) ≤ T⁺ (hs hz) tt`** (定理, 无前提). 输入 $0$ 与 $1$ 的实例是层 $1$ 与层 $2$, 都不含 $\Omega$-极限.
> - `change0 : Hs.ChangeHs hz tt`, `mono0 : Hs.MonoStepHs hz tt`: 两条前提在 $h=0$ 处的实例 (前提可满足).
>
> 方法: 层 $1$ 的 $\Omega_1=1⨾(\text{层 }0\text{ 的节点})$, 节点在第 0 层目标上上升 (两个实例里都可算), 链的各项都是**第 0 层的树**, 折叠它们只用到 `Run` 的五句 ($0$, $1$, $⨾$, ℕ-极限; 第 0 层的树没有节点和闭包) 与动作 (在作用点上都是 `Stp`). 所以只要第 0 层的树上的一个关系 `_⊑_` (同形, 极限逐点, 外加 "右边多接一段" `r+`), 状态在第 0 层目标上相关, 两个实例 (任意) 里的折叠输出就相关 (`Two.Run-R`, `Two.Chn-R`); 相关的树和在值上 $\le$ (`sum⊑`). 状态的差异 (大状态多出的段) 都落在 `r+` 上.
>
> 范围: 只对第 0 层的树. $h\ge1$ 时链的项是第 $\ge1$ 层的树 (含节点, 输出要在高目标上比), 本文的关系不覆盖; 那是 `MonoPort6` 一族在两种种类上的对应, 没有做.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpMonoOne where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (s≤; ≤l; l≤; ≤-refl; ≤-trans) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFClosed using (module At; T⁺; top⁺; one; W₁)
open import OCF.Align.HtTowerFGrow using (sum≥)
open import OCF.Align.TpMonoHs using (b₀; lW₁; module Hs)
```

## §1 第 0 层的树上的关系

```agda
infix 4 _⊑_
data _⊑_ {W : Wd₂} : D₀ W → D₀ W → Set where
  r0 : n0 ⊑ n0
  r1 : n1 ⊑ n1
  r⨾ : ∀ {x x′ y y′} → x ⊑ x′ → y ⊑ y′ → (x ⨾ y) ⊑ (x′ ⨾ y′)
  rl : ∀ {d d′ : ℕ → D₀ W} → (∀ n → d n ⊑ d′ n) → nl d ⊑ nl d′
  r+ : ∀ {x x′ z} → x ⊑ x′ → x ⊑ (x′ ⨾ z)

sum⊑ : ∀ {W} {x x′ : D₀ W} → x ⊑ x′ → ∀ {b b′} → b ≤ᴬ b′ → sum b x ≤ᴬ sum b′ x′
pt⊑  : ∀ {W} {d d′ : ℕ → D₀ W} → (∀ n → d n ⊑ d′ n) → ∀ {b b′} → b ≤ᴬ b′ → ∀ n → pt b d n ≤ᴬ pt b′ d′ n
sum⊑ r0 h = h
sum⊑ r1 h = s≤ h
sum⊑ (r⨾ p q) h = sum⊑ q (sum⊑ p h)
sum⊑ (rl e) h = l≤ (λ n → ≤l n (pt⊑ e h n))
sum⊑ (r+ {x′ = x′} {z = z} p) {b′ = b′} h = ≤-trans (sum⊑ p h) (sum≥ (sum b′ x′) z)
pt⊑ e h zero = h
pt⊑ e h (suc n) = sum⊑ (e n) (pt⊑ e h n)
```

## §2 两个实例里折叠第 0 层的树

```agda
module Two (Λ₁ : Ht) (l₁ : LgB Λ₁) (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁) (Λ₂ : Ht) (l₂ : LgB Λ₂) (o₂ : ∀ {w} → hs hz ⊲[ w ] Λ₂) where
  module P = At Λ₁ l₁ o₁
  module Q = At Λ₂ l₂ o₂

  -- 第 0 层目标上 (一切目标世界, 两边位置各自任意) 的输出相关
  DfR : ∀ {W} → P.Df W → Q.Df W → Set
  DfR {W} Δ Δ′ = ∀ {m} (T : P.Tg W hz m) (T′ : Q.Tg W hz m) → P.yc Δ T ⊑ Q.yc Δ′ T′

  StR : ∀ {W} → P.St W → Q.St W → Set
  StR Y Y′ = DfR (P.d Y) (Q.d Y′)

  IgR : ∀ {W} → P.Ig hz W → Q.Ig hz W → Set
  IgR {W} A₀ A₀′ = ∀ (lW : LgW₂ W) w w′ Y Y′ → StR Y Y′ → DfR (A₀ ≤rf lW w Y) (A₀′ ≤rf lW w′ Y′)

  ⊕R : ∀ {W} {Y : P.St W} {Y′ : Q.St W} (lW : LgW₂ W) {Δ : P.Df W} {Δ′ : Q.Df W} → StR Y Y′ → DfR Δ Δ′ →
       StR (P._⊕⟨_⟩_ Y lW Δ) (Q._⊕⟨_⟩_ Y′ lW Δ′)
  ⊕R lW r e T T′ = r⨾ (r T T′) (e T T′)

  Run-R : ∀ {W₀ W} (a₁ a₂ : AccY hz) {x x′ : D₀ W₀} → x ⊑ x′ → (q₁ q₂ : W₀ ≤ W) (lW : LgW₂ W) (ll₁ : P.LW hz W) (ll₂ : Q.LW hz W)
          {A₀ : P.Ig hz W} {A₀′ : Q.Ig hz W} → IgR A₀ A₀′ → ∀ (w w′ : D₀ W) {Y Y′} → StR Y Y′ →
          DfR (P.Run a₁ x q₁ lW ll₁ A₀ w Y) (Q.Run a₂ x′ q₂ lW ll₂ A₀′ w′ Y′)
  Rpt-R : ∀ {W₀ W} (a₁ a₂ : AccY hz) {d d′ : ℕ → D₀ W₀} → (∀ n → d n ⊑ d′ n) → (q₁ q₂ : W₀ ≤ W) (lW : LgW₂ W) (ll₁ : P.LW hz W) (ll₂ : Q.LW hz W)
          {A₀ : P.Ig hz W} {A₀′ : Q.Ig hz W} → IgR A₀ A₀′ → ∀ (w w′ : D₀ W) {Y Y′} → StR Y Y′ →
          ∀ n → StR (proj₂ (P.Rpt a₁ d q₁ lW ll₁ A₀ w Y n)) (proj₂ (Q.Rpt a₂ d′ q₂ lW ll₂ A₀′ w′ Y′ n))

  Run-R a₁ a₂ r0 q₁ q₂ lW ll₁ ll₂ hA w w′ r T T′ = r0
  Run-R a₁ a₂ r1 q₁ q₂ lW ll₁ ll₂ hA w w′ r T T′ = hA lW w w′ _ _ r T T′
  Run-R a₁ a₂ (r⨾ {x} {x′} p q) q₁ q₂ lW ll₁ ll₂ {A₀} {A₀′} hA w w′ {Y} {Y′} r T T′ =
    r⨾ (Run-R a₁ a₂ p q₁ q₂ lW ll₁ ll₂ hA w w′ r T T′)
       (Run-R a₁ a₂ q q₁ q₂ lW ll₁ ll₂ hA (w ⨾ nw q₁ x) (w′ ⨾ nw q₂ x′)
          {P._⊕⟨_⟩_ Y lW (P.Run a₁ x q₁ lW ll₁ A₀ w Y)} {Q._⊕⟨_⟩_ Y′ lW (Q.Run a₂ x′ q₂ lW ll₂ A₀′ w′ Y′)}
          (⊕R {Y = Y} {Y′ = Y′} lW {P.Run a₁ x q₁ lW ll₁ A₀ w Y} {Q.Run a₂ x′ q₂ lW ll₂ A₀′ w′ Y′} r (Run-R a₁ a₂ p q₁ q₂ lW ll₁ ll₂ hA w w′ r)) T T′)
  Run-R a₁ a₂ (rl {d} {d′} e) q₁ q₂ lW ll₁ ll₂ {A₀} {A₀′} hA w w′ {Y} {Y′} r T T′ =
    rl (λ n → Run-R a₁ a₂ (e n) q₁ q₂ lW ll₁ ll₂ hA (proj₁ (P.Rpt a₁ d q₁ lW ll₁ A₀ w Y n)) (proj₁ (Q.Rpt a₂ d′ q₂ lW ll₂ A₀′ w′ Y′ n))
                    {proj₂ (P.Rpt a₁ d q₁ lW ll₁ A₀ w Y n)} {proj₂ (Q.Rpt a₂ d′ q₂ lW ll₂ A₀′ w′ Y′ n)}
                    (Rpt-R a₁ a₂ e q₁ q₂ lW ll₁ ll₂ hA w w′ r n) T T′)
  Run-R a₁ a₂ (r+ p) q₁ q₂ lW ll₁ ll₂ hA w w′ r T T′ = r+ (Run-R a₁ a₂ p q₁ q₂ lW ll₁ ll₂ hA w w′ r T T′)

  Rpt-R a₁ a₂ e q₁ q₂ lW ll₁ ll₂ hA w w′ r zero = r
  Rpt-R a₁ a₂ {d} {d′} e q₁ q₂ lW ll₁ ll₂ {A₀} {A₀′} hA w w′ {Y} {Y′} r (suc n) =
    ⊕R {Y = proj₂ (P.Rpt a₁ d q₁ lW ll₁ A₀ w Y n)} {Y′ = proj₂ (Q.Rpt a₂ d′ q₂ lW ll₂ A₀′ w′ Y′ n)} lW {P.Run a₁ (d n) q₁ lW ll₁ A₀ (proj₁ (P.Rpt a₁ d q₁ lW ll₁ A₀ w Y n)) (proj₂ (P.Rpt a₁ d q₁ lW ll₁ A₀ w Y n))}
          {Q.Run a₂ (d′ n) q₂ lW ll₂ A₀′ (proj₁ (Q.Rpt a₂ d′ q₂ lW ll₂ A₀′ w′ Y′ n)) (proj₂ (Q.Rpt a₂ d′ q₂ lW ll₂ A₀′ w′ Y′ n))}
       (Rpt-R a₁ a₂ e q₁ q₂ lW ll₁ ll₂ hA w w′ r n)
       (Run-R a₁ a₂ (e n) q₁ q₂ lW ll₁ ll₂ hA (proj₁ (P.Rpt a₁ d q₁ lW ll₁ A₀ w Y n)) (proj₁ (Q.Rpt a₂ d′ q₂ lW ll₂ A₀′ w′ Y′ n))
          {proj₂ (P.Rpt a₁ d q₁ lW ll₁ A₀ w Y n)} {proj₂ (Q.Rpt a₂ d′ q₂ lW ll₂ A₀′ w′ Y′ n)}
          (Rpt-R a₁ a₂ e q₁ q₂ lW ll₁ ll₂ hA w w′ r n))

  -- 节点上升时的链: 各项与状态都相关
  Chn-R : ∀ {W} (a₁ a₂ : AccY hz) (hk₁ : P.LW hz W) (hk₂ : Q.LW hz W) (lW : LgW₂ W) {A₀ : P.Ig hz W} {A₀′ : Q.Ig hz W} → IgR A₀ A₀′ →
          ∀ {Y Y′} → StR Y Y′ → ∀ n →
          (proj₁ (proj₂ (P.Chn a₁ hk₁ lW A₀ Y n)) ⊑ proj₁ (proj₂ (Q.Chn a₂ hk₂ lW A₀′ Y′ n))) ×
          StR (proj₂ (proj₂ (P.Chn a₁ hk₁ lW A₀ Y n))) (proj₂ (proj₂ (Q.Chn a₂ hk₂ lW A₀′ Y′ n)))
  Chn-R a₁ a₂ hk₁ hk₂ lW hA r zero = r (P.tg ≤rf hk₁ lW) (Q.tg ≤rf hk₂ lW) , r
  Chn-R a₁ a₂ hk₁ hk₂ lW {A₀} {A₀′} hA {Y} {Y′} r (suc n) =
    Run-R a₁ a₂ (proj₁ ih) ≤rf ≤rf lW hk₁ hk₂ hA (proj₁ c₁) (proj₁ c₂) {proj₂ (proj₂ c₁)} {proj₂ (proj₂ c₂)} (proj₂ ih) (P.tg ≤rf hk₁ lW) (Q.tg ≤rf hk₂ lW) ,
    ⊕R {Y = proj₂ (proj₂ c₁)} {Y′ = proj₂ (proj₂ c₂)} lW {P.Run a₁ (proj₁ (proj₂ c₁)) ≤rf lW hk₁ A₀ (proj₁ c₁) (proj₂ (proj₂ c₁))} {Q.Run a₂ (proj₁ (proj₂ c₂)) ≤rf lW hk₂ A₀′ (proj₁ c₂) (proj₂ (proj₂ c₂))}
       (proj₂ ih) (Run-R a₁ a₂ (proj₁ ih) ≤rf ≤rf lW hk₁ hk₂ hA (proj₁ c₁) (proj₁ c₂) {proj₂ (proj₂ c₁)} {proj₂ (proj₂ c₂)} (proj₂ ih))
    where
    ih = Chn-R a₁ a₂ hk₁ hk₂ lW hA r n
    c₁ = P.Chn a₁ hk₁ lW A₀ Y n
    c₂ = Q.Chn a₂ hk₂ lW A₀′ Y′ n
```

## §3 $h = 0$

实例 $1=1\boxplus0$ (`T⁺ hz` 的, 记作 `I1`) 与 $2=1\boxplus1$ (`T⁺ (hs hz)` 的, `I2`). 三次比较都是 `Two` 的实例: `I1` 对 `I1` (实例之内), `I1` 对 `I2` (跨实例, 两次).

```agda
-- 状态读数里的两段
s₀ : ∀ {m} → D₀ m
s₀ = nl (λ _ → n1 ⨾ n0)

-- n0 ⨾ ω·(1 ⨾ 0) ⊑ 它自己接两段
pfx : ∀ {m} {z : D₀ m} → (n0 ⨾ s₀) ⊑ (((n0 ⨾ s₀) ⨾ n0) ⨾ z)
pfx = r+ (r+ (r⨾ r0 (rl (λ _ → r⨾ r1 r0))))

-- 同形的读数
same : ∀ {m} {z z′ : D₀ m} → z ⊑ z′ → (((n0 ⨾ s₀) ⨾ n0) ⨾ z) ⊑ (((n0 ⨾ s₀) ⨾ n0) ⨾ z′)
same r = r⨾ (r⨾ (r⨾ r0 (rl (λ _ → r⨾ r1 r0))) r0) r

module H0 = Hs hz tt

module I12 = Two (top⁺ hz) (Lg-⊞ {S₁} (hs hz) hz tt tt) (⊞-fst {S₁} (hs hz) hz) (top⁺ (hs hz)) (Lg-⊞ {S₁} (hs hz) (hs hz) tt tt) (⊞-fst {S₁} (hs hz) (hs hz))
module I11 = Two (top⁺ hz) (Lg-⊞ {S₁} (hs hz) hz tt tt) (⊞-fst {S₁} (hs hz) hz) (top⁺ hz) (Lg-⊞ {S₁} (hs hz) hz tt tt) (⊞-fst {S₁} (hs hz) hz)

-- 动作在作用点上都是 Stp: 只要状态相关, 输出相关
ig-Stp : ∀ {m} (Y Y′ : D₀ m) → Y ⊑ Y′ → (nl (λ _ → n1 ⨾ Y)) ⊑ (nl (λ _ → n1 ⨾ Y′))
ig-Stp Y Y′ r = rl (λ _ → r⨾ r1 r)

w₀₀ : Wd₂
w₀₀ = azero , hz

q₀₁ : w₀₀ ≤ W₁
q₀₁ = z⊲ one , hself
```

**实例之内 (`mono0`).** 左: `T⁺ hz` 的折叠 (世界 $(0,0)\to(1,0)$, 状态 $Y_0$, 基 $1$); 右: `X′` (世界 $(1,0)$, 状态 $Y_2$, 基 $b_0$). 节点上升时两边的链从状态在层 $0$ 上的读数起步, 左边 $0⨾\omega\cdot(1⨾0)$ 是右边的前缀 (`pfx`).

```agda
module M0 where
  open I11

  AL : P.Ig hz W₁
  AL = P.Ai accᴸ (accK {w₀₀} (ss hself)) (ss hself) (λ _ _ _ → n1) q₀₁ (hsuc hself) hself P.Act (n0 ⨾ nw q₀₁ n1)

  AR : Q.Ig hz W₁
  AR = Q.Ai accᴸ (accK {W₁} (ss hself)) (ss hself) (λ _ _ _ → n1) ≤rf (hsuc hself) hself Q.Act ((n0 ⨾ nw ≤rf n0) ⨾ nw ≤rf n1)

  igA : IgR AL AR
  igA lW w w′ Y Y′ r T T′ = ig-Stp _ _ (r T T′)

  YL : P.St W₁
  YL = P._⊕⟨_⟩_ P.Y₀ lW₁ (P.Act {top⁺ hz} ≤rf lW₁ n0 P.Y₀)

  YR : Q.St W₁
  YR = Q._⊕⟨_⟩_ H0.Y₂ᑫ lW₁ (Q.Act {top⁺ hz} ≤rf lW₁ (n0 ⨾ nw ≤rf n0) H0.Y₂ᑫ)

  rY : StR YL YR
  rY T T′ = pfx

  aL aR : AccY hz
  aL = accK {w₀₀} (ss hself)
  aR = accK {W₁} (ss hself)

  CL : ℕ → D₀ W₁ × (D₀ W₁ × P.St W₁)
  CL = P.Chn aL (hsuc hself) lW₁ AL YL

  CR : ℕ → D₀ W₁ × (D₀ W₁ × Q.St W₁)
  CR = Q.Chn aR (hsuc hself) lW₁ AR YR

  ch : ∀ n → (proj₁ (proj₂ (CL n)) ⊑ proj₁ (proj₂ (CR n))) × StR (proj₂ (proj₂ (CL n))) (proj₂ (proj₂ (CR n)))
  ch = Chn-R aL aR (hsuc hself) (hsuc hself) lW₁ {AL} {AR} igA {YL} {YR} rY

  rel : P.yc P.ΔΩ (P.τ₀ lW₁) ⊑ H0.X′
  rel = r⨾ (ig-Stp n0 ((n0 ⨾ s₀) ⨾ n0) (r+ (r+ r0)))
           (rl (λ n → Run-R aL aR (proj₁ (ch n)) ≤rf ≤rf lW₁ (hsuc hself) (hsuc hself) {AL} {AR} igA (proj₁ (CL n)) (proj₁ (CR n))
                          {proj₂ (proj₂ (CL n))} {proj₂ (proj₂ (CR n))} (proj₂ (ch n)) (P.τ₀ lW₁) (Q.τ₀ lW₁)))

mono0 : H0.MonoStepHs
mono0 = sum⊑ {x = I11.P.yc I11.P.ΔΩ (I11.P.τ₀ lW₁)} {x′ = H0.X′} M0.rel {b = one} {b′ = b₀} (sum≥ one (s₀ {W₁}))
```

**跨实例 (`change0`).** 左: `X′` (实例 $1$); 右: `X` (实例 $2$). 同一个世界、同一棵树、同形的状态; 节点的位置与比较的证据不同, 链的各项在两个实例里分别算出, 在第 0 层目标上相关.

```agda
base0 : ∀ {m} → ((n0 ⨾ s₀) ⨾ n0) ⊑ ((n0 ⨾ s₀ {m}) ⨾ n0)
base0 = r⨾ (r⨾ r0 (rl (λ _ → r⨾ r1 r0))) r0

module C0 where
  open I12

  ctx : D (hs hz) W₁
  ctx = (n0 ⨾ nw ≤rf n0) ⨾ nw ≤rf n1

  AL : P.Ig hz W₁
  AL = P.Ai accᴸ (accK {W₁} (ss hself)) (ss hself) (λ _ _ _ → n1) ≤rf (hsuc hself) hself P.Act ctx

  AR : Q.Ig hz W₁
  AR = Q.Ai (accK {w₀₀} (ss hself)) (accL hz) (ss hself) (λ _ _ _ → n1) ≤rf (hsuc (hsuc hself)) (hsuc hself) H0.A² ctx

  igA : IgR AL AR
  igA lW w w′ Y Y′ r T T′ = ig-Stp _ _ (r T T′)

  YL : P.St W₁
  YL = P._⊕⟨_⟩_ H0.Y₂ᑫ lW₁ (P.Act {top⁺ hz} ≤rf lW₁ (n0 ⨾ nw ≤rf n0) H0.Y₂ᑫ)

  YR : Q.St W₁
  YR = Q._⊕⟨_⟩_ H0.Y₂ᴾ lW₁ (H0.A² ≤rf lW₁ (n0 ⨾ nw ≤rf n0) H0.Y₂ᴾ)

  rY : StR YL YR
  rY T T′ = r⨾ base0 (ig-Stp _ _ base0)

  aL aR : AccY hz
  aL = accK {W₁} (ss hself)
  aR = accL hz

  CL : ℕ → D₀ W₁ × (D₀ W₁ × P.St W₁)
  CL = P.Chn aL (hsuc hself) lW₁ AL YL

  CR : ℕ → D₀ W₁ × (D₀ W₁ × Q.St W₁)
  CR = Q.Chn aR (hsuc (hsuc hself)) lW₁ AR YR

  ch : ∀ n → (proj₁ (proj₂ (CL n)) ⊑ proj₁ (proj₂ (CR n))) × StR (proj₂ (proj₂ (CL n))) (proj₂ (proj₂ (CR n)))
  ch = Chn-R aL aR (hsuc hself) (hsuc (hsuc hself)) lW₁ {AL} {AR} igA {YL} {YR} rY

  rel : H0.X′ ⊑ H0.X
  rel = r⨾ (ig-Stp _ _ base0)
           (rl (λ n → Run-R aL aR (proj₁ (ch n)) ≤rf ≤rf lW₁ (hsuc hself) (hsuc (hsuc hself)) {AL} {AR} igA (proj₁ (CL n)) (proj₁ (CR n))
                          {proj₂ (proj₂ (CL n))} {proj₂ (proj₂ (CR n))} (proj₂ (ch n)) (P.τ₀ lW₁) (Q.τ₀ lW₁)))

change0 : H0.ChangeHs
change0 = sum⊑ {x = H0.X′} {x′ = H0.X} C0.rel {b = b₀} {b′ = b₀} (≤-refl b₀)
```

## §4 结论

```agda
-- T⁺ 在输入 0 到 1 严格增长 (无前提)
T⁺0<T⁺1 : asuc (T⁺ hz tt) ≤ᴬ T⁺ (hs hz) tt
T⁺0<T⁺1 = H0.hs-reduce change0 mono0
```
