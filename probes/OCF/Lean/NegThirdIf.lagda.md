# 第三种组织, 否定一路 (二): 接口 `ThirdIf` 的盲区与边界

> 不含记号. 入口 [NegThird](NegThird.lagda.md). 只读导入构造一路的接口 [ThirdIf](ThirdIf.lagda.md) ("接口定稿 2026-11-06 21:21"), [CRwBase](CRwBase.lagda.md), 否定一路的 [NegRecBPre](NegRecBPre.lagda.md), [NegLHRecPre](NegLHRecPre.lagda.md), [NegThirdPre](NegThirdPre.lagda.md) (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **接口与 `LHRec` §4 的差.** 塔 `Tw U m` 的高度 $m$ 是 `HB U` 的值, $\Omega$-结点 `hΩ κ g` 给 `sup (E U κ)` (分量由坐标编号), **没有内层指标种类**: 底种类留在塔里. 新证据 `Pos U w m κ`: 塔的种类穿过高度的 $\Omega$-结点时, 分量坐标要在世界的界之下. 一层的移动 `LayerMv U` 与 `LHRecIf` 对一层同形.
>
> **结果.**
>
> 1. **位置 (§1).** 正面: **`Pos↑`** (对世界单调), **`embP`**, **`Pos-emb`** (沿第一位置嵌入, 带证据, 保位置). 否定: **`pos-wdep`** (同一高度同一种类, 世界 $(v,1)$ 有位置, $(v,0)$ 没有; 对一切 `S`); **`pos-dec→LPO`** (判定位置是 LPO); **`Ill.no-pos`** (分量下标不合法的种类在**一切**合法世界里没有位置); **`Twop.emb-not-unique`** (同一对高度, 两条第一位置证据, 两个不同的种类: 嵌入读证据, 不读高度).
> 2. **盲 (§2).** `Blind.stay`: 可入恒真, 世界不动, 回灌恒为 $0$, 是实例 (`stay-frozen`). `KrS.J`: Kripke 式, 对任一合法化 `lg` 是实例; **`sh-frozen`**: 回灌的进入不动低层世界. 所以接口不要求低层世界移动, 不要求进入的坐标被界住, 不要求回灌依赖坐标.
> 3. **回灌必须合法化 (§3).** `fb-must-legalize`, `no-plain-sh`: 新界是 $e+1$ 时回灌的值合法, 不能是 $B\boxplus c$. (同 `NegLHRecIf`, 对一层.)
> 4. **低层世界冻结时位置到不了 (§4).** **`frozen-no-pos`**: 对任一 `Frozen` 的实例, 从低层界为 $0$ 的世界出发, 任意多次回灌的进入 (`Run`) 之后, 高度 $\Omega$ 的分量 $1$ 的种类仍没有位置. 所以真要穿过高度的 $\Omega$-结点, 低层世界必须移动; 接口没有说它怎么移动 (判断: 这是 `NegThirdPre` §5 写回问题的入口).
> 5. **洗 (§5, 构造一路点名的目标).** **`no-wash`**: 全函数 $\mathrm{wash}_B$ 上 `Tw U m₁` 的值, 若输出的根带位置, 且输入的根带位置时留住根的种类, 则 LPO. 证明同 `HtTotalNeg.no-clamp`: 从位置证据里读极限下标.
>
> **前提实例.** 1: `pos-wdep` 的世界合法 (写在结论里), $v$ 取 `S⊥` 的 `tt`; `Ill` 的 $v$ 任取. 2: `Rf` 由 `rf-⊥`, `rf-step` 给出; `lg` 可取 $c\mapsto0$. 4: `Blind.stay` 与 `KrS.J` 都 `Frozen` (`stay-frozen`, `sh-frozen`). 5: 两条前提各自可满足: `wash-const` (恒 $0$, 根没有结点), `wash-id-keep` (恒等).
>
> **只否定什么.** 1 只否定判定位置与无证据的嵌入; **不否定**带证据的 `embP`. 2 不否定接口, 只说律不约束. 4 只否定低层世界冻结的实例. 5 只否定这一对性质 (根带位置 + 留住带位置的根); **不否定**把根的种类换掉的洗法, 坐标带证据的新种类结构, 在折叠实际发出的坐标上才成立的性质. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegThirdIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
import Data.Bool
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf
open import OCF.Lean.NegRecBPre using (Ωˢ; Lg-Ωˢ; one; module Top; no-s⊲z; hz-only)
open import OCF.Lean.NegLHRecPre using (module Fb)
open import OCF.Lean.NegThirdPre using (LPO; Dec₀; bd-dec→LPO; num; hit; bα; Bα; Lg-Bα; hit→; →hit)
open LayerMv
```

## §1 位置: 对世界单调, 依赖世界, 不能判定

```agda
module _ {U : KS} where
  Pos↑ : ∀ {w w′} → _≤w_ U w w′ → ∀ m κ → Pos U w m κ → Pos U w′ m κ
  Pos↑ q hz κ p = tt
  Pos↑ q (hs x) (inj₁ κ) p = Pos↑ q x κ p
  Pos↑ q (hs x) (inj₂ _) p = tt
  Pos↑ q (hl f) (n , κ) p = Pos↑ q (f n) κ p
  Pos↑ q (hΩ κ₀ g) (e , κ) (b , p) = Bd↑ U q b , Pos↑ q (g e) κ p

  -- 沿第一位置的嵌入 (带证据), 保位置
  embP : ∀ {a m w} → a ⊲[ w ] m → K (Tw U a) → K (Tw U m)
  embP hself κ = κ
  embP (hsuc p) κ = inj₁ (embP p κ)
  embP (hlim n p) κ = n , embP p κ
  embP (hLim {c = e} b p) κ = e , embP p κ

  Pos-emb : ∀ {a m w} (p : a ⊲[ w ] m) κ → Pos U w a κ → Pos U w m (embP p κ)
  Pos-emb hself κ h = h
  Pos-emb (hsuc p) κ h = Pos-emb p κ h
  Pos-emb (hlim n p) κ h = Pos-emb p κ h
  Pos-emb (hLim b p) κ h = b , Pos-emb p κ h

module P₁ {S : KS} (v : Wd S) where
  U : KS
  U = step S

  m₁ : HB U
  m₁ = Ωˢ {S}

  κ₁ : K (Tw U m₁)
  κ₁ = one {S} , inj₂ tt

  pos-1 : Pos U (v , one) m₁ κ₁
  pos-1 = hself , tt

  no-0 : ¬ Pos U (v , hz) m₁ κ₁
  no-0 (b , _) = no-s⊲z b

pos-wdep : ∀ {S : KS} (v : Wd S) → LgW S v →
  LgS S (v , one) × LgS S (v , hz) × Pos (step S) (v , one) (P₁.m₁ {S} v) (P₁.κ₁ v) × ¬ Pos (step S) (v , hz) (P₁.m₁ {S} v) (P₁.κ₁ v)
pos-wdep {S} v lv = (lv , tt) , (lv , tt) , P₁.pos-1 v , P₁.no-0 v

pos-dec→LPO : (∀ B → LgB {S⊥} B → Dec₀ (Pos (step S⊥) (tt , B) (P₁.m₁ {S⊥} tt) (P₁.κ₁ tt))) → LPO
pos-dec→LPO d = bd-dec→LPO λ B lB → go (d B lB)
  where
  go : ∀ {B : Cd} → Dec₀ (Pos (step S⊥) (tt , B) (P₁.m₁ {S⊥} tt) (P₁.κ₁ tt)) → Dec₀ (hs hz ⊲ B)
  go (inj₁ (b , _)) = inj₁ b
  go (inj₂ n) = inj₂ (λ b → n (b , tt))
```

**不合法的分量没有位置.** 高度 $\Omega$ 的分量下标取遍低一层的一切值, 含不合法的; 合法世界里合法的界之下没有不合法的值. 所以塔里有在**一切**合法世界里都没有位置的种类.

```agda
module Ill {S : KS} (v : Wd S) where
  U : KS
  U = step S

  badc : HB S
  badc = Fb.bad {S} v

  κb : K (Tw U (Ωˢ {S}))
  κb = badc , 0 , inj₂ tt

  no-pos : ∀ {W : Wd U} → LgW U W → ¬ Pos U W (Ωˢ {S}) κb
  no-pos (lv , lB) (b , _) = Fb.no-ev-bad {S} v lv lB b
```

**同一个第一位置, 两条证据, 两个种类.** 嵌入读的是证据, 不是一对高度.

```agda
module Twop where
  U : KS
  U = step S⊥

  m₂ : HB U
  m₂ = hΩ (inj₂ tt) (λ _ → hs hz)

  W₂ : Wd U
  W₂ = tt , hs (hs hz)

  Lg-m₂ : LgB m₂
  Lg-m₂ = (λ lw e e′ p → hself) , (λ lw e → tt)

  p₀ p₁ : hs hz ⊲[ W₂ ] m₂
  p₀ = hLim {c = hz} (hsuc (hsuc hself)) hself
  p₁ = hLim {c = hs hz} (hsuc hself) hself

  κ′ : K (Tw U (hs hz))
  κ′ = inj₂ tt

  emb-not-unique : ¬ (embP p₀ κ′ ≡ embP p₁ κ′)
  emb-not-unique ()
```

## §2 接口的盲区

世界序自反不是 `KS` 的字段; 下面的实例以自反为前提, `S⊥` 与它的 `step` 上成立.

```agda
Rf : KS → Set
Rf U = ∀ (w : Wd U) → _≤w_ U w w

rf-⊥ : Rf S⊥
rf-⊥ w = tt

rf-step : ∀ {U} → Rf U → Rf (step U)
rf-step r (w , B) = r w , hself

module Blind (U : KS) (rf : Rf U) (u₀ : Wd U) (lu : LgW U u₀) where
  rfS : ∀ (W : WS U) → LeS U W W
  rfS W = rf-step rf W

  stay : LayerMv U
  stay = record
    { Adm = λ _ _ → ⊤ ; nxt = λ W e a → W ; sh = λ W c → hz
    ; adm-sh = λ c lW → tt ; nx-up = λ {W} a → rfS W ; lg-nx = λ a l → l
    ; adm↓ = λ q a′ → tt , q
    ; W₀ = u₀ , hs hz ; o₀ = hself ; lW₀ = lu , tt }

  stay-frozen : ∀ W e a → nxt stay W e a ≡ W
  stay-frozen W e a = refl
```

**Kripke 式, 带合法化.** 同 `NegLHRecIf.Kr`, 对一层. 低层世界 $u'$ 是可入证据里给的, 接口**不要求** $u'$ 严格变大. `adm-sh` 给的是 $u'=u$.

```agda
module KrS (U : KS) (rf : Rf U) (u₀ : Wd U) (lu : LgW U u₀) (lg : HB U → HB U) (Lg : ∀ c → LgB (lg c)) where
  rfS : ∀ (W : WS U) → LeS U W W
  rfS W = rf-step rf W

  AdmK : WS U → HB U → Set
  AdmK W e = Σ (Wd U) (λ u′ → _≤w_ U (proj₁ W) u′ × LgW U u′ × (proj₂ W ⊲[ u′ ] e) × LgB e)

  J : LayerMv U
  J = record
    { Adm = AdmK ; nxt = λ W e a → proj₁ a , hs e ; sh = λ W c → proj₂ W ⊞ lg c
    ; adm-sh = λ {W} c lW → proj₁ W , rf (proj₁ W) , proj₁ lW , ⊞-fst (proj₂ W) (lg c) , Lg-⊞ (proj₂ W) (lg c) (proj₂ lW) (Lg c)
    ; nx-up = λ a → proj₁ (proj₂ a) , hsuc (proj₁ (proj₂ (proj₂ (proj₂ a))))
    ; lg-nx = λ a lW → proj₁ (proj₂ (proj₂ a)) , proj₂ (proj₂ (proj₂ (proj₂ a)))
    ; adm↓ = λ {W} {W′} q {e} a′ →
        (proj₁ a′ , ≤w-tr U (proj₁ q) (proj₁ (proj₂ a′)) , proj₁ (proj₂ (proj₂ a′)) ,
          ⊲ᴮ-tr (⊲ᴮ↑ (proj₁ (proj₂ a′)) (proj₂ q)) (proj₁ (proj₂ (proj₂ (proj₂ a′)))) , proj₂ (proj₂ (proj₂ (proj₂ a′)))) ,
        rfS (proj₁ a′ , hs e)
    ; W₀ = u₀ , hs hz ; o₀ = hself ; lW₀ = lu , tt }

  nb-J : ∀ W e a → proj₂ (nxt J W e a) ≡ hs e
  nb-J W e a = refl

  -- 回灌给的可入证据里低层世界不动
  sh-frozen : ∀ W c lW → proj₁ (nxt J W (sh J W c) (adm-sh J c lW)) ≡ proj₁ W
  sh-frozen W c lW = refl
```

## §3 回灌必须合法化

```agda
fb-must-legalize : ∀ {U} (I : LayerMv U) → (∀ W e a → proj₂ (nxt I W e a) ≡ hs e) →
  ∀ {W} → LgS U W → ∀ c → LgB (sh I W c)
fb-must-legalize I nb {W} lW c =
  subst LgB (nb W (sh I W c) (adm-sh I c lW)) (proj₂ (lg-nx I (adm-sh I c lW) lW))

no-plain-sh : ∀ {U} (I : LayerMv U) (u : Wd U) → LgW U u → (∀ W e a → proj₂ (nxt I W e a) ≡ hs e) →
  ¬ (∀ W c → sh I W c ≡ proj₂ W ⊞ c)
no-plain-sh {U} I u lu nb eq =
  Fb.no-plain-fb {U} u (subst LgB (eq (u , hz) (Fb.bad {U} u)) (fb-must-legalize I nb {u , hz} (lu , tt) (Fb.bad {U} u)))
```

## §4 低层世界冻结时位置到不了

`Frozen I`: 回灌的进入不动低层世界 (`KrS.J`, `Blind.stay` 都是). 这时从一个世界出发, 经任意多次回灌的进入, 低层世界不变. 所以穿过高度 $\Omega$-结点 (种类在 $U$ 里) 的位置只由出发的低层世界决定: 低层世界里界为 $0$ 的种类 (下例), 高度 $\Omega$ 的分量 $1$ 的种类永远没有位置.

```agda
Frozen : ∀ {U} → LayerMv U → Set
Frozen {U} I = ∀ W c (l : LgS U W) → proj₁ (nxt I W (sh I W c) (adm-sh I c l)) ≡ proj₁ W

data Run {U} (I : LayerMv U) : WS U → WS U → Set where
  rz : ∀ {W} → Run I W W
  rs : ∀ {W W′} c (l : LgS U W) → Run I (nxt I W (sh I W c) (adm-sh I c l)) W′ → Run I W W′

run-frozen : ∀ {U} (I : LayerMv U) → Frozen I → ∀ {W W′} → Run I W W′ → proj₁ W′ ≡ proj₁ W
run-frozen I fr rz = refl
run-frozen I fr (rs {W} c l r) = Eq.trans (run-frozen I fr r) (fr W c l)
  where import Relation.Binary.PropositionalEquality as Eq

frozen-no-pos : ∀ {S : KS} (I : LayerMv (step S)) → Frozen I → (v : Wd S) → ∀ {W′} →
  Run I ((v , hz) , hs hz) W′ → ¬ Pos (step S) (proj₁ W′) (P₁.m₁ {S} v) (P₁.κ₁ v)
frozen-no-pos {S} I fr v r p = P₁.no-0 v (subst (λ z → Pos (step S) z (P₁.m₁ {S} v) (P₁.κ₁ v)) (run-frozen I fr r) p)
```

## §5 没有位置的坐标上: 全函数的 "洗" 是 LPO

构造一路的头号卡点 (它的判断): 留下的塔新种类的分支在任意输出坐标 $c$ 处要读输入, $c$ 里可能有分量坐标不在界之下的种类. `wash`: 把 `Tw U m₁` 的值洗成根带位置的值. 只要 "输出的根带位置" 且 "输入的根带位置时留住根的种类", 就是 LPO. 世界取 $(\mathrm{tt}, B)$, $B$ 合法; 种类 $\kappa_1$ 的位置就是 $1\lhd B$.

```agda
private
  U₁ : KS
  U₁ = step S⊥
  m₁ : HB U₁
  m₁ = P₁.m₁ {S⊥} tt
  κ₁ : K (Tw U₁ m₁)
  κ₁ = P₁.κ₁ tt

T₁ : KS
T₁ = Tw U₁ m₁

RPos : Cd → HB T₁ → Set
RPos B (hΩ κ g) = Pos U₁ (tt , B) m₁ κ
RPos B _ = ⊤

tix : ∀ {a b : Cd} → a ⊲ b → ℕ
tix (hlim n _) = n
tix _ = 0

idx : (B : Cd) → (x : HB T₁) → RPos B x → ℕ
idx B hz r = 0
idx B (hs x) r = 0
idx B (hl f) r = 0
idx B (hΩ κ g) r = tix (proj₁ r)

idx-tr : ∀ {B x y} (e : x ≡ y) (r : RPos B x) → idx B x r ≡ idx B y (subst (RPos B) e r)
idx-tr refl r = refl

hitb : ∀ b → hs {S⊥} hz ⊲ (Data.Bool.if_then_else_ b (hs hz) hz) → b ≡ true
hitb true p = refl
hitb false ()

tix-hit : ∀ α (p : hs hz ⊲ Bα α) → hit α (tix p) ≡ true
tix-hit α (hlim n q) = hitb (hit α n) q

no-wash : (wash : (B : Cd) → LgB B → HB T₁ → HB T₁) →
  (∀ B lB c → RPos B (wash B lB c)) →
  (∀ B lB g → Pos U₁ (tt , B) m₁ κ₁ → Σ (E T₁ κ₁ → HB T₁) (λ g′ → wash B lB (hΩ κ₁ g) ≡ hΩ κ₁ g′)) →
  LPO
no-wash wash rp keep α = go (hit α i) refl
  where
  B = Bα α
  lB = Lg-Bα α
  c₀ : HB T₁
  c₀ = hΩ κ₁ (λ _ → hz)
  i : ℕ
  i = idx B (wash B lB c₀) (rp B lB c₀)
  found : Σ ℕ (λ n → α n ≡ true) → hit α i ≡ true
  found (n , e) with keep B lB (λ _ → hz) (Pos₁ n e)
    where
    Pos₁ : ∀ n → α n ≡ true → Pos U₁ (tt , B) m₁ κ₁
    Pos₁ n e = hlim n (one⊲ (hit α n) (→hit α n e)) , tt
      where
      one⊲ : ∀ b → b ≡ true → hs {S⊥} hz ⊲ (Data.Bool.if_then_else_ b (hs hz) hz)
      one⊲ true _ = hself
  ... | g′ , eq = subst (λ j → hit α j ≡ true) (sym (idx-tr eq (rp B lB c₀)))
                    (tix-hit α (proj₁ (subst (RPos B) eq (rp B lB c₀))))
  go : (b : Bool) → hit α i ≡ b → Σ ℕ (λ n → α n ≡ true) ⊎ (∀ n → α n ≡ false)
  go true e = inj₁ (hit→ α i e)
  go false e = inj₂ λ n → t→f (α n) (λ t → f≢t (Eq.trans (Eq.sym e) (found (n , t))))
    where
    import Relation.Binary.PropositionalEquality as Eq
    f≢t : ¬ (false ≡ true)
    f≢t ()
    t→f : ∀ b → ¬ (b ≡ true) → b ≡ false
    t→f false k = refl
    t→f true k = ⊥-elim (k refl)

-- 前提各自可满足
wash-const : ∀ B c → RPos B ((λ (_ : HB T₁) → hz) c)
wash-const B c = tt

wash-id-keep : ∀ (B : Cd) (lB : LgB B) g → Σ (E T₁ κ₁ → HB T₁) (λ g′ → (λ (x : HB T₁) → x) (hΩ κ₁ g) ≡ hΩ κ₁ g′)
wash-id-keep B lB g = g , refl
```

## 结论 (按档)

- **[定理, 正面]** `Pos↑`, `embP`, `Pos-emb`; `Blind.stay`, `KrS.J`, `rf-⊥`, `rf-step`.
- **[定理, 否定]** **`pos-wdep`**, **`pos-dec→LPO`**, **`Ill.no-pos`**, **`Twop.emb-not-unique`**; `fb-must-legalize`, `no-plain-sh`; **`frozen-no-pos`** (`run-frozen`); **`no-wash`**.
- **[判断]** 低层世界怎么移动是写回问题; 读法没有定理.
