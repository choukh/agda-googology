# 路径记在折叠输出上, 否定一路 (二): lΩ 层号的坐标, 有公共上界才可比, 没有就连精确的决定都不存在

> 不含记号. 入口 [NegPathOut](NegPathOut.lagda.md). 本篇**不依赖**构造一路的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FEᴸ` 只在标 "条件" 的定理里作前提.
>
> **问题.** [Fab4LOm](Fab4LOm.lagda.md) 的 `exact→Sep`: 在层号 $X_1=$ `lΩ lz G` 上, 若对**一切**坐标 $c$ 都有精确的决定 (`Exact`), 则分离子 `Sep`. 本篇问: 这个前提可满足吗? 精确的决定在单个坐标上存在吗? 公共上界给出什么?
>
> **结果.**
>
> 1. **`cmp-bound` (定理, 构造).** 两个可数坐标 $c, c'$ 在同一合法界 $L$ 之下, 则它们读成的层号字面可比 (`CmpL`: 一个是另一个的字面子层号 `⊑ᴸ`). 由 `cmpB` 与 `ofC-mono`.
> 2. **`incomp-lim` (定理).** 两个坐标都是有限高度的 ℕ-极限, 首项不同 (例如 $\lim\mathrm{od}$ 与 $\lim\mathrm{ev}$; 或 $\lim(1,1,\dots)$ 与 $\lim(0,0,\dots)$), 则它们的层号**字面不可比**. 推论 **`no-join-lim`**: 它们没有合法的字面公共上界 (与 `HtTowerNeg.no-joinᴮ` 一致, 这里由 1, 2 合出).
> 3. **`exact→cmp` (定理, 对一切层号与种类).** 精确的决定蕴含种类的层号与目标字面可比. 推论 **`no-exact-lim`**: 在 $X_1$ 上, 目标是 $\lim v$ 的层号 (经坐标 $\lim v$ 在 $X_1$ 之下), 种类是 $\lim u$ 的新种类, $u$, $v$ 如 2, 则**没有**精确的决定 (不是推出 `Sep`, 是推出 $\bot$). 两个坐标都合法.
> 4. **`fab4-premise-false` (定理).** Fab4LOm `exact→Sep` 的前提 ("对一切 $c$ 精确") 在它自己的 $X_1$, $t_1$ 上**不可满足**: 取 $c_1=\lim(1,1,\dots)$ (合法). 所以 `exact→Sep` 在 $X_1$ 上什么也没说 (AGENTS "前提要可满足"); 那里的结论应改读成本篇的 3. Fab4LOm 的 `exact₂` 是另一个层号 $X_2$ (分支不依赖坐标) 上的实例, 不是 $X_1$ 上的.
> 5. **`cmpdec→Sep′` (定理), `cmpdec→WLPO` (定理, 条件 `FEᴸ`).** 若折叠想加第四种结果 "不可比" 并正确地报告它, 就要判定 "合法坐标的层号与目标 $t_1$ 可比否"; 这推出分离子 `Sep′` (对单调合法的一族 $a'_\alpha$), 有外延时推出 WLPO.
>
> **前提实例.** 1: 任一合法 $L$ 与它的两个第一位置 (例如 $L=\lim\mathrm{ev}$, $c=c'=0$). 2, 3: `od-ev` ($\lim\mathrm{od}$, $\lim\mathrm{ev}$, 都合法: `Lg-od`, `Lg-ev`) 与 `c₁-t₀` ($c_1$, $t_0$, 都合法: `Lg-c₁`, `Lg-t₀`). 5: `CmpDec` 经典成立 (层号字面可比是一个命题, 经典可判定); 在 Agda 里证不出 (同 `NegTySupSel.pt-sep` 的档, 判断). `FEᴸ` 是函数外延的一个实例, 与本系统相容.
>
> **只否定什么.** 只否定: (a) $X_1$ 上对**这些**坐标对的字面精确决定 (`Exact`, 或任何蕴含字面可比的判据); (b) 正确报告 "不可比" 的决定 (到分离子 / 条件 WLPO). **不否定**: 带字面公共上界的坐标对上的比较 (`cmp-bound` 是构造, Fab4LOm 的 `om-step` 是构造); 只在折叠实际访问的、带公共上界的坐标上作决定的折叠; 按值 (非字面) 的判据 (本篇没有值的定理). 本篇没有关闭任何路线.
>
> **对 "路径记在输出上" 的意思 (判断, 依据 1-3).** 层号经 `lΩ` 的不同坐标进来时, 能不能决定只看两个坐标有没有合法的公共上界; 有, 字面可比 (1); 没有, 连精确决定都不存在 (3). 所以路径的作用只在于**提供公共上界**: 链点 $b\boxplus d_n$ 都在同一条链的后来的界之下 ([NegPathOutPath](NegPathOutPath.lagda.md) `chain-common`), 可以; 但折叠在**留下的** $\Omega$-结点处对一切坐标递归 (`TySupFold.Φ` 的 `keep` 一支), 那里的坐标与目标的坐标一般没有公共上界, 路径记在输出上管不到输入的这些分支. (接口定稿后的注: 构造一路的 `PathOutFold.Ψ` 进入一切分支前先 `shift` 到界之上, 输入谓词 `PH` 要种类坐标在界之下, 于是每次 `dec` 都带公共上界; 见 [NegPathOutInst](NegPathOutInst.lagda.md) 的 `tri-IX₁`. 代价落在输入上: `ph-lg-own`.)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegPathOutCmp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv; lvl)
open import OCF.Align.TySupIf using (Dc; keep; same; above)
open import OCF.Align.TySupC using (ofC)
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; Lg-ev; Lg-od; NatH; nat-ev; nat-od)
open import OCF.Align.Fab4LOm
  using (_⊑ᴸ_; _⊏ᴸ_; ⊑self; ⊑suc; ⊑lim; ⊑om; ⊑ᴸ-tr; ls-inj; ll-inj; Exact; X₁; G; κ; t₀; t₁; pt₁; bit; bitz)
```

## §1 有限层号, 字面可比

```agda
FinL : LH → Set
FinL lz = ⊤
FinL (ls x) = FinL x
FinL (ll _) = ⊥
FinL (lΩ _ _) = ⊥

fin⊑ : ∀ {a b} → a ⊑ᴸ b → FinL b → FinL a
fin⊑ ⊑self f = f
fin⊑ (⊑suc p) f = fin⊑ p f
fin⊑ (⊑lim n p) ()
fin⊑ (⊑om c p) ()

natFin : ∀ (x : HB S⊥) → NatH x → FinL (ofC x)
natFin hz _ = tt
natFin (hs x) n = natFin x n
natFin (hl _) ()
natFin (hΩ () _) _

ofc-inj : ∀ (x y : HB S⊥) → NatH x → NatH y → ofC x ≡ ofC y → x ≡ y
ofc-inj hz hz _ _ _ = refl
ofc-inj hz (hs y) _ _ ()
ofc-inj (hs x) hz _ _ ()
ofc-inj (hs x) (hs y) nx ny e = cong hs (ofc-inj x y nx ny (ls-inj e))
ofc-inj (hl _) y () ny e
ofc-inj (hΩ () _) y nx ny e
ofc-inj x (hl _) nx () e
ofc-inj x (hΩ () _) nx ny e

-- 进入 ℕ-极限层号的字面子层号: 要么就是它, 要么在某一项之下
into : ∀ {a b} → a ⊑ᴸ b → ∀ {f} → b ≡ ll f → (a ≡ ll f) ⊎ Σ ℕ (λ n → a ⊑ᴸ f n)
into ⊑self e = inj₁ e
into (⊑lim n q) refl = inj₂ (n , q)
into (⊑suc _) ()
into (⊑om _ _) ()

CmpL : LH → LH → Set
CmpL a b = (a ⊑ᴸ b) ⊎ (b ⊑ᴸ a)
```

## §2 公共上界之下: 字面可比 (构造)

```agda
ofC-mono : ∀ {c c′ : HB S⊥} → c ⊲[ tt ] c′ → ofC c ⊑ᴸ ofC c′
ofC-mono hself = ⊑self
ofC-mono (hsuc p) = ⊑suc (ofC-mono p)
ofC-mono (hlim n p) = ⊑lim n (ofC-mono p)
ofC-mono (hLim {κ = ()} _ _)

cmp-bound : ∀ {c c′ L : HB S⊥} → c ⊲[ tt ] L → c′ ⊲[ tt ] L → LgB L → CmpL (ofC c) (ofC c′)
cmp-bound p q l with cmpB p q tt l
... | inj₁ r = inj₂ (ofC-mono r)
... | inj₂ r = inj₁ (ofC-mono r)
```

## §3 有限项的 ℕ-极限, 首项不同: 字面不可比

```agda
module _ (u v : ℕ → HB S⊥) (nu : ∀ n → NatH (u n)) (nv : ∀ n → NatH (v n)) (ne : ¬ (u 0 ≡ v 0)) where
  private
    half : ∀ (u′ v′ : ℕ → HB S⊥) → (∀ n → NatH (u′ n)) → (∀ n → NatH (v′ n)) → ¬ (u′ 0 ≡ v′ 0) →
           ¬ (ofC (hl u′) ⊑ᴸ ofC (hl v′))
    half u′ v′ nu′ nv′ ne′ p with into p refl
    ... | inj₁ e = ne′ (ofc-inj (u′ 0) (v′ 0) (nu′ 0) (nv′ 0) (cong (λ h → h 0) (ll-inj e)))
    ... | inj₂ (n , q) = fin⊑ q (natFin (v′ n) (nv′ n))

  incomp-lim : ¬ CmpL (ofC (hl u)) (ofC (hl v))
  incomp-lim (inj₁ p) = half u v nu nv ne p
  incomp-lim (inj₂ p) = half v u nv nu (λ e → ne (sym e)) p

  no-join-lim : ¬ Σ (HB S⊥) (λ L → LgB L × (hl u ⊲[ tt ] L) × (hl v ⊲[ tt ] L))
  no-join-lim (L , l , p , q) = incomp-lim (cmp-bound p q l)
```

## §4 精确的决定蕴含字面可比; 不可比处没有精确的决定

`Exact` 是 Fab4LOm 的: 留 ⇒ 种类的层号严格在目标下; 同层 ⇒ 相等; 在上 ⇒ 所报的层就是种类的层号且目标严格在它下面. 三条都给出字面可比. 对一切层号 $X$ 与种类.

```agda
exact→cmp : ∀ {X t} {k : K (Lv X)} (d : Dc Lv _⊏ᴸ_ _⊑ᴸ_ X t k) → Exact k d → CmpL (lvl X k) t
exact→cmp (keep _ _) lt = inj₁ (⊑ᴸ-tr (⊑suc ⊑self) lt)
exact→cmp {X} {t} {k} (same _) e = inj₁ (subst (λ z → lvl X k ⊑ᴸ z) e ⊑self)
exact→cmp {t = t} (above i _ _ _) (ei , lt) = inj₂ (⊑ᴸ-tr (⊑suc ⊑self) (subst (λ z → ls t ⊑ᴸ z) ei lt))
```

**定理 `no-exact-lim`.** $X_1$ 上, 目标是 $\lim v$ 的层号, 种类是 $\lim u$ 处的新种类 (`κ (hl u)`, 层号 `ofC (hl u)`): 任何决定都不精确.

```agda
no-exact-lim : ∀ (u v : ℕ → HB S⊥) → (∀ n → NatH (u n)) → (∀ n → NatH (v n)) → ¬ (u 0 ≡ v 0) →
  (d : Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₁ (ofC (hl v)) (κ (hl u))) → ¬ Exact (κ (hl u)) d
no-exact-lim u v nu nv ne d ex = incomp-lim u v nu nv ne (exact→cmp {X₁} d ex)

-- 目标确实在 X₁ 之下 (经坐标 lim v)
pt-lim : ∀ (v : ℕ → HB S⊥) → ofC (hl v) ⊑ᴸ X₁
pt-lim v = ⊑om (hl v) (⊑suc ⊑self)
```

**实例.** $\lim\mathrm{od}$ 对 $\lim\mathrm{ev}$; $c_1=\lim(1,1,\dots)$ 对 $t_0=\lim(0,0,\dots)$. 四个坐标都合法.

```agda
s≢z : ¬ (hs {S⊥} hz ≡ hz)
s≢z ()

no-exact-od-ev : (d : Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₁ (ofC (hl evᴴ)) (κ (hl odᴴ))) → ¬ Exact (κ (hl odᴴ)) d
no-exact-od-ev = no-exact-lim odᴴ evᴴ nat-od nat-ev s≢z

no-join-od-ev : ¬ Σ (HB S⊥) (λ L → LgB L × (hl odᴴ ⊲[ tt ] L) × (hl evᴴ ⊲[ tt ] L))
no-join-od-ev = no-join-lim odᴴ evᴴ nat-od nat-ev s≢z

u₁ v₁ : ℕ → HB S⊥
u₁ _ = hs hz
v₁ _ = hz

c₁ : HB S⊥
c₁ = hl u₁

Lg-c₁ : LgB c₁
Lg-c₁ = (λ n → hself) , (λ n → tt)

Lg-t₀ : LgB t₀
Lg-t₀ = (λ n → hself) , (λ n → tt)

no-exact-c₁ : (d : Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₁ t₁ (κ c₁)) → ¬ Exact (κ c₁) d
no-exact-c₁ = no-exact-lim u₁ v₁ (λ _ → tt) (λ _ → tt) s≢z
```

**定理 `fab4-premise-false`.** Fab4LOm `exact→Sep` 的前提在 $X_1$, $t_1$ 上不可满足.

```agda
fab4-premise-false : (d : ∀ c → Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₁ t₁ (κ c)) → ¬ (∀ c → Exact (κ c) (d c))
fab4-premise-false d ex = no-exact-c₁ (d c₁) (ex c₁)
```

## §5 第四种结果 "不可比": 判定它推出分离子

单调合法的一族: $\beta_\alpha(n)=\alpha_0\vee\dots\vee\alpha_n$, $a'_\alpha=\lim_n[\beta_\alpha(n)]$. $a'_\alpha$ 的层号与 $t_1$ 字面可比当且仅当 (经典地) $\alpha$ 全假. `CmpDec`: 对一切合法坐标, 判定它的层号与 $t_1$ 是否字面可比.

```agda
β : (ℕ → Bool) → ℕ → Bool
β α zero = α 0
β α (suc n) = β α n ∨ α (suc n)

a′ : (ℕ → Bool) → HB S⊥
a′ α = hl (λ n → bit (β α n))

Lg-a′ : ∀ α → LgB (a′ α)
Lg-a′ α = (λ {w} n → st {w} (β α n) (α (suc n))) , (λ n → lgbit (β α n))
  where
  st : ∀ {w} x y → bit x ⊲[ w ] bit (x ∨ y)
  st true y = hself
  st {w} false y = z⊲ᴮ {w = w} (bit y)
  lgbit : ∀ x → LgB (bit x)
  lgbit true = tt
  lgbit false = tt

∨-r : ∀ x y → x ∨ y ≡ false → y ≡ false
∨-r true y ()
∨-r false y e = e

βF→αF : ∀ α n → β α n ≡ false → α n ≡ false
βF→αF α zero e = e
βF→αF α (suc n) e = ∨-r (β α n) (α (suc n)) e

αF→βF : ∀ α → (∀ n → α n ≡ false) → ∀ n → β α n ≡ false
αF→βF α h zero = h 0
αF→βF α h (suc n) rewrite αF→βF α h n = h (suc n)

finBit : ∀ x → FinL (ofC (bit x))
finBit true = tt
finBit false = tt

CmpDec : Set
CmpDec = ∀ (c : HB S⊥) → LgB c → CmpL (ofC c) t₁ ⊎ ¬ CmpL (ofC c) t₁

eqF : ∀ α → ofC (a′ α) ≡ t₁ → ∀ n → α n ≡ false
eqF α e n = βF→αF α n (bitz (β α n) (cong (λ h → h n) (ll-inj e)))

cmp→αF : ∀ α → CmpL (ofC (a′ α)) t₁ → ∀ n → α n ≡ false
cmp→αF α (inj₁ p) with into p refl
... | inj₁ e = eqF α e
... | inj₂ (n , q) = ⊥-elim (fin⊑ q tt)
cmp→αF α (inj₂ p) with into p refl
... | inj₁ e = eqF α (sym e)
... | inj₂ (n , q) = ⊥-elim (fin⊑ q (finBit (β α n)))

Sep′ : Set
Sep′ = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (ofC (a′ α) ≡ t₁)

cmpdec→Sep′ : CmpDec → Sep′
cmpdec→Sep′ dec α with dec (a′ α) (Lg-a′ α)
... | inj₁ cm = inj₁ (cmp→αF α cm)
... | inj₂ ncm = inj₂ (λ e → ncm (inj₁ (subst (λ z → ofC (a′ α) ⊑ᴸ z) e ⊑self)))

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)

FEᴸ : Set
FEᴸ = ∀ (f g : ℕ → LH) → (∀ n → f n ≡ g n) → f ≡ g

-- 条件: FEᴸ
cmpdec→WLPO : FEᴸ → CmpDec → WLPO
cmpdec→WLPO fe dec α with cmpdec→Sep′ dec α
... | inj₁ allF = inj₁ allF
... | inj₂ ne = inj₂ (λ allF → ne (cong ll (fe _ _ (λ n → cong (λ b → ofC (bit b)) (αF→βF α allF n)))))
```

## 结论 (按档)

- **[定理]** `FinL`, `fin⊑`, `natFin`, `ofc-inj`, `into`, `CmpL`; `ofC-mono`, **`cmp-bound`** (构造); **`incomp-lim`**, **`no-join-lim`**; **`exact→cmp`** (对一切层号); **`no-exact-lim`**, `pt-lim`, `no-exact-od-ev`, `no-join-od-ev`, `no-exact-c₁`, `Lg-c₁`, `Lg-t₀`; **`fab4-premise-false`**; `β`, `a′`, `Lg-a′`, **`cmpdec→Sep′`**.
- **[条件定理]** **`cmpdec→WLPO`** (条件 `FEᴸ`).
- **[判断]** `Sep′`, `CmpDec` 经典成立而在 Agda 里证不出; "$\lim\mathrm{od}$ 与 $\lim\mathrm{ev}$ 的层号按值相同 (都读 $\omega$), 所以按值应当是同层" 是判断, 本篇没有值的定理; "留下的结点处的分支是墙所在" (文件头末段) 是判断, 依据 1-3, 接口定稿后对实例查.
