# RaiseC (三): "一起升" 与 `FBA` 的律

> 不含记号. 入口 [RaiseC](RaiseC.lagda.md). 对象是以坐标 `A` 为下标的积世界 `SA = Lev {S₀} (hΩ tt (λ _ → hz))`, 它定义相等于 `sup A (λ _ → S₀)`: 世界是 `A → A`, 种类 $(c_0,\mathrm{tt})$ 的界是第 $c_0$ 个分量. 这正是 "下标是坐标, 判定不了是不是这个分量" 的情形 (`NegGenFoldUpd`).
>
> 1. **`upAll-≤`, `upAll-lg`, `upAll-tp` (条件: 给定 `RaiseA`).** `ProdA.upAll` 满足 `rs≤` (要分量与 $v$ 合法, `FBA.rs≤` 不要), `rsLg`, 以及**只在** $W\,i\lhd v$ (与合法) 下的 `tp-rs` (`FBA.tp-rs` 是无条件的). 前提 `RaiseA` 只经典地可满足 (`RaiseCBd.dec→Raise`).
> 2. **`no-fba-upAll` (定理, 否定).** 对**一切** $R:A\to A\to A$ 与一切种类 $(c_0,\mathrm{tt})$: 不存在 `FBA SA (c₀ , tt)` 使 `tpA` 读第 $c_0$ 个分量且 `rsA` 是 `upAll` 的形状 ($i\mapsto R\,(W\,i)\,v$). 理由: 无条件的 `tp-rs` 让 $R$ "总含 $v$", `rs≤` (在第 $c_0$ 个分量是 $0$ 的世界里) 给 `R-lo`, `rsLg` 给合法, 撞 `RaiseCBase.no-always`. 所以 **"一起升" 必须离开 `FBA` 的字面律**: 至少把 `tp-rs` 换成带前提 $\mathrm{tpA}\,w\lhd v$ 的形状. 前提可满足: `FBA SA (azero , tt)` 有实例 (`fba₀`, 在可判定的点 $0$ 上点更新), 所以否定的是 `upAll` 形状, 不是 `FBA`.
> 3. **`no-bounded-raise` (定理, 否定).** 不管是不是 `upAll` 形状: 一个世界上的升界操作若 (i) 在 $W\,c_0\lhd v$ 时不降任何分量, (ii) 第 $c_0$ 个分量含 $v$, (iii) 把有字面公共上界的合法世界送到有字面公共上界的世界, 则撞 `no-joinA`. 三条两两可满足 (`pair-12`, `pair-23`, `pair-13`). 所以有界版 (`RaiseCBd.Rᵇ`) 只能处理 $v$ 已在公共上界之下的情形; $v$ 不在时, 没有任何升界能保住公共上界.
> 4. **`fixed-bound-no-tp` (定理).** 若 `tpA` 总在一个固定的 $\Lambda$ 之下, 无条件的 `tp-rs` 不成立 ($v=\Lambda+1$).
> 5. **`upAllᵇ` (构造, 无条件) 与它的律, 实例 `exᵇ`.** 世界的分量与 $v$ 都在合法的 $\Lambda$ 之下时, 逐分量取 `Rᵇ`: 不降 (`upᵇ-≤`), 合法 (`upᵇ-lg`), 仍在 $\Lambda$ 之下 (`upᵇ-bd`), **每个**分量都含 $v$ (`upᵇ-tp`, 无前提), 是满足这些的最小世界 (`upᵇ-least`). 具体实例: `SA` 的世界 `sepW azero ωe` (第 $0$ 个分量是 $0$, 其余是 $\omega_e=\lim(0,2,4,\dots)$), $\Lambda=\omega_e$, $v=2$: 升后第 $0$ 个分量是 $2$, 其余仍是 $\omega_e$ (`exᵇ-0`, `exᵇ-1`, `refl`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RaiseCFba where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲; lg⊲; Strict; ss)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (evA; odA; Lg-evA; Lg-odA; no-joinA)
open import OCF.Align.GenFoldIf using (FBA; tpA; rsA; rs≤; rsLg; tp-rs)
open import OCF.Align.RaiseIf using (RaiseA; R; R-lo; R-hi; R-lg; module ProdA)
open import OCF.Align.RaiseCBase using (no-always; oneA; S⊲; irrS)
open import OCF.Align.RaiseCBd using (Rᵇ; Rᵇ-lo; Rᵇ-hi; Rᵇ-Λ; Rᵇ-lg; Rᵇ-least)
```

## §0 以 `A` 为下标的积世界

```agda
SA : KS
SA = Lev {S₀} (hΩ tt (λ _ → hz))

-- 定义相等: 世界是 A → A, 序与合法逐分量, 种类 (c , tt) 的界是第 c 个分量
WdSA : Wd SA ≡ (A → A)
WdSA = refl

≤SA : ∀ (w w′ : Wd SA) → _≤w_ SA w w′ ≡ (∀ c → w c ⊲ w′ c)
≤SA w w′ = refl

LgSA : ∀ (w : Wd SA) → LgW SA w ≡ (∀ c → Lg (w c))
LgSA w = refl

BdSA : ∀ c₀ x (w : Wd SA) → Bd SA (c₀ , tt) x w ≡ (x ⊲ w c₀)
BdSA c₀ x w = refl
```

**把一个分量与别的分量分开的世界.** 下标的头 ($0$, 后继, 极限) 可判定. `sepW c₀ a`: 与 $c_0$ 同头的分量取 $0$, 其余取 $a$; `other c₀` 与 $c_0$ 不同头.

```agda
sepW : A → A → A → A
sepW azero a azero = azero
sepW azero a (asuc _) = a
sepW azero a (alim _) = a
sepW (asuc _) a azero = a
sepW (asuc _) a (asuc _) = azero
sepW (asuc _) a (alim _) = a
sepW (alim _) a azero = a
sepW (alim _) a (asuc _) = a
sepW (alim _) a (alim _) = azero

other : A → A
other azero = oneA
other (asuc _) = azero
other (alim _) = azero

sep-at : ∀ c₀ a → sepW c₀ a c₀ ≡ azero
sep-at azero a = refl
sep-at (asuc _) a = refl
sep-at (alim _) a = refl

sep-other : ∀ c₀ a → sepW c₀ a (other c₀) ≡ a
sep-other azero a = refl
sep-other (asuc _) a = refl
sep-other (alim _) a = refl

sep⊲ : ∀ c₀ a c → sepW c₀ a c ⊲ a
sep⊲ azero a azero = z⊲ a
sep⊲ azero a (asuc _) = C.self
sep⊲ azero a (alim _) = C.self
sep⊲ (asuc _) a azero = C.self
sep⊲ (asuc _) a (asuc _) = z⊲ a
sep⊲ (asuc _) a (alim _) = C.self
sep⊲ (alim _) a azero = C.self
sep⊲ (alim _) a (asuc _) = C.self
sep⊲ (alim _) a (alim _) = z⊲ a

sep-lg : ∀ c₀ {a} → Lg a → ∀ c → Lg (sepW c₀ a c)
sep-lg c₀ la c = lg⊲ (sep⊲ c₀ _ c) la
```

## §1 给定 `RaiseA` 时 `upAll` 满足的律 (条件)

```agda
open ProdA A

module UpLaws (ρ : RaiseA) where
  upAll-≤ : ∀ {W v} → LgP W → Lg v → W ≤ᴾ upAll ρ W v
  upAll-≤ lW lv i = R-lo ρ (lW i) lv

  upAll-lg : ∀ {W v} → LgP W → Lg v → LgP (upAll ρ W v)
  upAll-lg lW lv i = R-lg ρ (lW i) lv

  -- tp-rs 只在 W i ⊲ v 下 (FBA.tp-rs 无条件)
  upAll-tp : ∀ {W v} i → LgP W → Lg v → W i ⊲ v → v ⊲ upAll ρ W v i
  upAll-tp i lW lv p = R-hi ρ (lW i) lv p

  -- 读成 SA 的种类 (c₀ , tt): rs≤ 要合法前提, tp-rs 要前提 tpA w ⊲ v
  rs≤ᶜ : ∀ c₀ {w : Wd SA} {v} → LgW SA w → Lg v → w c₀ ⊲ v → _≤w_ SA w (upAll ρ w v)
  rs≤ᶜ c₀ lw lv _ = upAll-≤ lw lv

  tp-rsᶜ : ∀ c₀ {w : Wd SA} {v} → LgW SA w → Lg v → w c₀ ⊲ v → Bd SA (c₀ , tt) v (upAll ρ w v)
  tp-rsᶜ c₀ lw lv p = upAll-tp c₀ lw lv p
```

## §2 `upAll` 形状满足不了 `FBA` 的字面律 (对一切 $R$)

```agda
no-fba-upAll : ∀ c₀ (F : FBA SA (c₀ , tt)) (G : A → A → A) →
  (∀ w → tpA F w ≡ w c₀) → (∀ w v c → rsA F w v c ≡ G (w c) v) → ⊥
no-fba-upAll c₀ F G tpEq rsEq = no-always G lo gd al
  where
  al : ∀ {a v} → Lg a → Lg v → v ⊲ G a v
  al {a} {v} _ _ = subst (v ⊲_) (trans (tpEq (rsA F (λ _ → a) v)) (rsEq (λ _ → a) v c₀)) (tp-rs F {λ _ → a} {v})
  lo : ∀ {a v} → Lg a → Lg v → a ⊲ G a v
  lo {a} {v} _ _ =
    subst (λ z → z ⊲ G z v) (sep-other c₀ a)
      (subst (sepW c₀ a (other c₀) ⊲_) (rsEq (sepW c₀ a) v (other c₀))
        (rs≤ F {sepW c₀ a} {v} (subst (_⊲ v) (sym (trans (tpEq (sepW c₀ a)) (sep-at c₀ a))) (z⊲ v)) (other c₀)))
  gd : ∀ {a v} → Lg a → Lg v → Lg (G a v)
  gd {a} {v} la lv = subst Lg (rsEq (λ _ → a) v c₀) (rsLg F {λ _ → a} {v} (λ _ → la) lv c₀)
```

**前提可满足 (`FBA` 本身有实例).** 在可判定的点 $c_0 = 0$ 上点更新: 第 $0$ 个分量换成 $v$, 其余不动.

```agda
ptU : (A → A) → A → A → A
ptU w v azero = v
ptU w v (asuc c) = w (asuc c)
ptU w v (alim f) = w (alim f)

fba₀ : FBA SA (azero , tt)
fba₀ = record
  { tpA = λ w → w azero
  ; rsA = ptU
  ; rs≤ = λ { p azero → p ; p (asuc c) → C.self ; p (alim f) → C.self }
  ; rsLg = λ { lw lv azero → lv ; lw lv (asuc c) → lw (asuc c) ; lw lv (alim f) → lw (alim f) }
  ; tp-rs = C.self }
```

`fba₀` 不是 `upAll` 形状 (它看下标的头). 对头不可判定地区分的 $c_0$ (例如两个都是极限的下标), 点更新要判定 $c\equiv c_0$; `NegGenFoldUpd.upd₁-sep` 说明连同 "留" 一起要就推出分离子. 本篇不否定一般 $c_0$ 上的 `FBA` (判断: 它要 "只让第 $c_0$ 个分量含 $v$" 的操作, 与 "留" 同型; 未编译).

## §3 有公共上界的世界: 任何升界都保不住上界

```agda
Bnd : (A → A) → Set
Bnd w = Σ A (λ Λ → Lg Λ × (∀ c → w c ⊲ Λ))

Le Tp Bk : A → ((A → A) → A → (A → A)) → Set
Le c₀ rs = ∀ {w v} → w c₀ ⊲ v → ∀ c → w c ⊲ rs w v c
Tp c₀ rs = ∀ {w v} → v ⊲ rs w v c₀
Bk c₀ rs = ∀ {w v} → (∀ c → Lg (w c)) → Lg v → Bnd w → Bnd (rs w v)

no-bounded-raise : ∀ c₀ rs → Le c₀ rs → Tp c₀ rs → Bk c₀ rs → ⊥
no-bounded-raise c₀ rs le tp bk = no-joinA (Λ′ , lΛ′ , ev⊲ , od⊲)
  where
  w : A → A
  w = sepW c₀ (alim evA)
  bnd : Bnd w
  bnd = alim evA , Lg-evA , sep⊲ c₀ (alim evA)
  B′ = bk {w} {alim odA} (sep-lg c₀ Lg-evA) Lg-odA bnd
  Λ′ = proj₁ B′
  lΛ′ = proj₁ (proj₂ B′)
  w0 : w c₀ ⊲ alim odA
  w0 = subst (_⊲ alim odA) (sym (sep-at c₀ (alim evA))) (z⊲ (alim odA))
  ev⊲ : alim evA ⊲ Λ′
  ev⊲ = ⊲-tr (subst (_⊲ rs w (alim odA) (other c₀)) (sep-other c₀ (alim evA)) (le w0 (other c₀))) (proj₂ (proj₂ B′) (other c₀))
  od⊲ : alim odA ⊲ Λ′
  od⊲ = ⊲-tr (tp {w} {alim odA}) (proj₂ (proj₂ B′) c₀)
```

**三条两两可满足.** (i)+(ii): 每个分量换成以 $(W\,c, v)$ 开头的 ℕ-极限 (不合法, 但 (i), (ii) 不要合法); (ii)+(iii): 世界换成常值 $v$; (i)+(iii): 世界不动.

```agda
pr : A → A → ℕ → A
pr x y zero = x
pr x y (suc _) = y

pair-12 : ∀ c₀ → Le c₀ (λ w v c → alim (pr (w c) v)) × Tp c₀ (λ w v c → alim (pr (w c) v))
pair-12 c₀ = (λ _ c → C.lim 0 C.self) , C.lim 1 C.self

pair-23 : ∀ c₀ → Tp c₀ (λ w v c → v) × Bk c₀ (λ w v c → v)
pair-23 c₀ = C.self , (λ {w} {v} lw lv _ → v , lv , (λ c → C.self))

pair-13 : ∀ c₀ → Le c₀ (λ w v → w) × Bk c₀ (λ w v → w)
pair-13 c₀ = (λ _ c → C.self) , (λ lw lv b → b)
```

## §4 固定上界下无条件的 `tp-rs` 不成立

```agda
fixed-bound-no-tp : ∀ {W : Set} (tp : W → A) (rs : W → A → W) (Λ : A) → (∀ w → tp w ⊲ Λ) → W →
  ¬ (∀ w v → v ⊲ tp (rs w v))
fixed-bound-no-tp tp rs Λ bd w₀ all =
  irrS Λ (S⊲ (ss C.self) (⊲-tr (all w₀ (asuc Λ)) (bd (rs w₀ (asuc Λ)))))
```

## §5 有界的一起升 (构造)

世界的每个分量与 $v$ 都在合法的 $\Lambda$ 之下 (证据作参数, 对一切下标类型 $I$).

```agda
module ProdBd (I : Set) {Λ : A} (lΛ : Lg Λ) where
  upAllᵇ : (W : I → A) → (∀ i → W i ⊲ Λ) → (v : A) → v ⊲ Λ → I → A
  upAllᵇ W bW v q i = Rᵇ (bW i) q lΛ

  module _ (W : I → A) (bW : ∀ i → W i ⊲ Λ) (v : A) (q : v ⊲ Λ) where
    upᵇ-≤ : ∀ i → W i ⊲ upAllᵇ W bW v q i
    upᵇ-≤ i = Rᵇ-lo (bW i) q lΛ

    upᵇ-lg : ∀ i → Lg (upAllᵇ W bW v q i)
    upᵇ-lg i = Rᵇ-lg (bW i) q lΛ

    upᵇ-bd : ∀ i → upAllᵇ W bW v q i ⊲ Λ
    upᵇ-bd i = Rᵇ-Λ (bW i) q lΛ

    -- 每个分量都含 v, 无前提
    upᵇ-tp : ∀ i → v ⊲ upAllᵇ W bW v q i
    upᵇ-tp i = Rᵇ-hi (bW i) q lΛ

    -- 最小: 任何不降且含 v 的世界都在它之上
    upᵇ-least : ∀ (W′ : I → A) → (∀ i → W i ⊲ W′ i) → (∀ i → v ⊲ W′ i) → ∀ i → upAllᵇ W bW v q i ⊲ W′ i
    upᵇ-least W′ le tp i = Rᵇ-least (bW i) q lΛ (le i) (tp i)
```

**实例 (`SA` 的世界).** $\omega_e = \lim(0,2,4,\dots)$ (`alim evA`), 世界 `sepW azero ωe`, $v = 2$.

```agda
ωe two : A
ωe = alim evA
two = asuc (asuc azero)

two⊲ωe : two ⊲ ωe
two⊲ωe = C.lim 1 C.self

open ProdBd A {alim evA} Lg-evA

exᵇ : Wd SA
exᵇ = upAllᵇ (sepW azero ωe) (sep⊲ azero ωe) two two⊲ωe

exᵇ-0 : exᵇ azero ≡ two
exᵇ-0 = refl

exᵇ-1 : exᵇ oneA ≡ ωe
exᵇ-1 = refl

exᵇ-ω : exᵇ ωe ≡ ωe
exᵇ-ω = refl

-- 作为 SA 的世界: 比原世界大, 合法, 种类 (azero , tt) 的界含 2
exᵇ-≥ : _≤w_ SA (sepW azero ωe) exᵇ
exᵇ-≥ = upᵇ-≤ (sepW azero ωe) (sep⊲ azero ωe) two two⊲ωe

exᵇ-lg : LgW SA exᵇ
exᵇ-lg = upᵇ-lg (sepW azero ωe) (sep⊲ azero ωe) two two⊲ωe

exᵇ-tp : Bd SA (azero , tt) two exᵇ
exᵇ-tp = upᵇ-tp (sepW azero ωe) (sep⊲ azero ωe) two two⊲ωe azero
```
