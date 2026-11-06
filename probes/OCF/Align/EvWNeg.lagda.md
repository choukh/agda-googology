# 事件历史世界 (二): 重放依赖证据 (拷贝墙的定理形式)

> 不含记号. 入口 [EvW](EvW.lagda.md). 诊断 §2.4 预计: 世界的下标换成 (坐标, 证据) 后, 拷贝问题以 "重放对证据的依赖" 回来. 这一篇在 `S₀` 上给一个具体的合法外层世界, 一个事件, 一个坐标的两个证据, 两次重放的界**既不相等, 也互不为第一位置** (在任何内层世界里).
>
> - **`no-indep`** (否定): "对一切合法外层世界, 同一坐标两个证据下重放的界相等或一方是另一方的第一位置" 不成立.
> - **`no-cmp∃`** (否定): 若把界写成 "存在一个证据使 $x$ 在重放的界之下" (种类不带证据, 只是坐标), 则界之下的两个格不总可比; 所以 `KS` 的 `cmpK` 在这种种类上没有. 这是诊断 §3.3 "`cmpK` 要证据相等" 的定理形式.
> - **方向仍与证据无关** (`EvWBase.dir-indep`, 定理). 不同的只是累加时的路径: 这里是 `hlim 0 hself` 对 `hlim 1 hself`, `emb⊲` 把同一个增量送进 `sup ℕ` 的第 0 与第 1 个分量.
>
> **只否定什么.** 只否定 `EvWBase.Rp.rp` 这一种重放 (沿 `cmpB` 给出的路径用 `emb⊲` 累加) 对一切合法外层世界与证据无关, 以及以它为界的无证据种类上的比较. **不否定**: 带证据的种类 (`EvWBase.EvKS`, 已构造); 每个坐标取规范证据的重放; 分支的单调数据 "相干" (同一目标给同一路径) 的外层世界上的无关性; 不经 `cmpB` 路径的其他累加方式. 反例用到: 分支 $g$ 不单射 ($g(1)=g(\omega_A)=\omega_0$), 且单调数据按目标坐标选进 $\omega_0$ 的不同项. 这是合法数据 (`LgB` 是数据, 不是命题).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvWNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.UniTrBase using (inv-hΩ)
open import OCF.Align.EvWBase
```

## §1 外层世界

坐标的第二数类高度 $\omega_0=\mathrm{hl}(\lambda\_.\,0)$ (常值列, 合法). 外层界 $b=\Omega$-节点, 分支 $g$: $g(0)=0$, 其余 $g(x)=\omega_0$. 单调数据 `mg`: 从 $0$ 到后继坐标走 $\omega_0$ 的第 0 项, 到极限坐标走第 1 项; 其余是自环. 外层世界 $a_0=\mathrm{alim}(\lambda\_.\,1)$.

```agda
ω₀ : HB S₀
ω₀ = hl (λ _ → hz)

lω₀ : LgB ω₀
lω₀ = (λ n → hself) , (λ n → tt)

g : A → HB S₀
g azero = hz
g (asuc _) = ω₀
g (alim _) = ω₀

mg : ∀ {w} (x x′ : A) → x ⊲ x′ → g x ⊲[ w ] g x′
mg azero azero _ = hself
mg azero (asuc _) _ = hlim 0 hself
mg azero (alim _) _ = hlim 1 hself
mg (asuc _) azero ()
mg (asuc _) (asuc _) _ = hself
mg (asuc _) (alim _) _ = hself
mg (alim _) azero ()
mg (alim _) (asuc _) _ = hself
mg (alim _) (alim _) _ = hself

lgg : ∀ x → LgB (g x)
lgg azero = tt
lgg (asuc _) = lω₀
lgg (alim _) = lω₀

bΩ : HB S₀
bΩ = hΩ tt g

lbΩ : LgB bΩ
lbΩ = (λ {w} {x} {x′} lw e e′ pr → mg x x′ pr) , (λ x _ → lgg x)

a₀ : A
a₀ = alim (λ _ → asuc azero)

la₀ : Lg a₀
la₀ = (λ n → C.self) , (λ n → tt)
```

## §2 一个事件, 一个坐标的两个证据

事件: 坐标 $0$ (经 $g(0)$), 增量 $\Omega_z=\Omega$-节点 (常值 $0$ 分支, 合法). 坐标 $\omega_0$ 的两个证据: 经坐标 $1$ (`p₁`) 与经坐标 $a_0$ (`p₂`). 两次重放都是 `refl` 算出来的.

```agda
open Rp {S₀} a₀ bΩ la₀ lbΩ

p₁ p₂ : ω₀ ⊲[ a₀ ] bΩ
p₁ = hLim {c = asuc azero} (C.lim 0 C.self) hself
p₂ = hLim {c = a₀} C.self hself

pz : hz ⊲[ a₀ ] bΩ
pz = hLim {c = azero} (z⊲ a₀) hself

Ωz : HB S₀
Ωz = hΩ tt (λ _ → hz)

lΩz : LgB Ωz
lΩz = (λ lw e e′ pr → hself) , (λ x _ → tt)

H₁ : Hist
H₁ = ev hz pz Ωz lΩz ∷ []

R₁ R₂ : HB (Lev ω₀)
R₁ = hΩ (0 , tt) (λ _ → hz)
R₂ = hΩ (1 , tt) (λ _ → hz)

rp₁ : rp H₁ ω₀ p₁ ≡ R₁
rp₁ = refl

rp₂ : rp H₁ ω₀ p₂ ≡ R₂
rp₂ = refl

-- 方向相同 (都累加), 路径不同
dir₁₂ : Same (cmpS p₁ pz) (cmpS p₂ pz)
dir₁₂ = tt

path₁ : cmpS p₁ pz ≡ inj₁ (hlim 0 hself)
path₁ = refl

path₂ : cmpS p₂ pz ≡ inj₁ (hlim 1 hself)
path₂ = refl
```

## §3 两个界不相等, 互不为第一位置

```agda
idx : HB (Lev ω₀) → ℕ
idx (hΩ κ _) = proj₁ κ
idx _ = 7

private
  0≢1 : ¬ (0 ≡ 1)
  0≢1 ()

R-ne : ¬ (R₁ ≡ R₂)
R-ne e = 0≢1 (cong idx e)

R₁⋬R₂ : ∀ {v} → ¬ (R₁ ⊲[ v ] R₂)
R₁⋬R₂ p with inv-hΩ p
... | inj₁ e = R-ne e
... | inj₂ (c , _ , ())

R₂⋬R₁ : ∀ {v} → ¬ (R₂ ⊲[ v ] R₁)
R₂⋬R₁ p with inv-hΩ p
... | inj₁ e = R-ne (sym e)
... | inj₂ (c , _ , ())
```

## §4 两条否定

```agda
Rel : (c : HB S₀) → HB (Lev c) → HB (Lev c) → Set
Rel c x y = (x ≡ y) ⊎ (Σ (Wd (Lev c)) (λ v → x ⊲[ v ] y) ⊎ Σ (Wd (Lev c)) (λ v → y ⊲[ v ] x))

Indep : Set
Indep = ∀ {a b} (la : Lg a) (lb : LgB b) H c (p p′ : c ⊲[ a ] b) →
        Rel c (Rp.rp {S₀} a b la lb H c p) (Rp.rp {S₀} a b la lb H c p′)

no-indep : ¬ Indep
no-indep I with I la₀ lbΩ H₁ ω₀ p₁ p₂
... | inj₁ e = R-ne e
... | inj₂ (inj₁ (v , q)) = R₁⋬R₂ q
... | inj₂ (inj₂ (v , q)) = R₂⋬R₁ q
```

**无证据的种类没有比较.** 界写成 "存在证据": $x$ 在坐标 $c$ 处有界, 若有某个 $p$ 使 $x\lhd$ `rp H c p`. 内层世界合法也不救.

```agda
Cmp∃ : Set
Cmp∃ = ∀ {a b} (la : Lg a) (lb : LgB b) H c (v : Wd (Lev c)) → LgW (Lev c) v → ∀ x x′ →
       Σ (c ⊲[ a ] b) (λ p → x ⊲[ v ] Rp.rp {S₀} a b la lb H c p) →
       Σ (c ⊲[ a ] b) (λ p′ → x′ ⊲[ v ] Rp.rp {S₀} a b la lb H c p′) →
       (x′ ⊲[ v ] x) ⊎ (x ⊲[ v ] x′)

v₀ : Wd (Lev ω₀)
v₀ = λ _ → azero

lv₀ : LgW (Lev ω₀) v₀
lv₀ = λ _ → tt

no-cmp∃ : ¬ Cmp∃
no-cmp∃ K∃ with K∃ la₀ lbΩ H₁ ω₀ v₀ lv₀ R₁ R₂ (p₁ , hself) (p₂ , hself)
... | inj₁ q = R₂⋬R₁ q
... | inj₂ q = R₁⋬R₂ q
```

**前提可满足.** 外层世界合法 (`la₀`, `lbΩ`), 事件增量合法 (`lΩz`), 内层世界合法 (`lv₀`), 两个证据与事件证据都是闭项 (`p₁`, `p₂`, `pz`). **正对照**: 带证据的种类 (`EvKS`) 把 $(\omega_0,p_1)$ 与 $(\omega_0,p_2)$ 当成两个种类, 每个种类的界之下照常可比 (`EvKS.cmpKᵉ`), 不需要上面的 `Cmp∃`.

## §5 重放依赖外层界的合法证明; 外层长高时合法证明要相干

`LgB` 是数据: 同一个外层界 $b_\Omega$ 的另一份合法证明 `lbΩ′` 把单调数据的两个方向对调. 同一事件表, 同一证据, 换合法证明, 重放的界从 $R_1$ 变成 $R_2$ (`no-lb-indep`). 推论: 外层界沿后继长高 ($b\mapsto\mathrm{hs}\,b$, `LgB (hs b)` 定义地就是 `LgB b`) 时, 若新界的合法证明不是旧的那一份, 重放可以变成不可比 (`no-wk`). 正对照: 合法证明不变时重放不变 (`EvWBase.WkSuc.wk-suc`, `Wk⊞.wk-⊞`).

**只否定什么.** 只否定 "重放与外层界的合法证明无关" 与 "外层沿后继长高, 合法证明任取, 重放与旧的相等或可比". 不否定合法证明相干的长高 (那是 `wk-⊞`, 定理). 它说明: 以重放为界的世界若要随外层世界长高, 外层界的合法证明必须是**世界的数据**, 而且长高要保持它 (`step` 的世界把 `LgB` 放在命题 `LgW` 里, 不在序 `_≤⁺_` 里, 这一点要改).

```agda
mg′ : ∀ {w} (x x′ : A) → x ⊲ x′ → g x ⊲[ w ] g x′
mg′ azero azero _ = hself
mg′ azero (asuc _) _ = hlim 1 hself
mg′ azero (alim _) _ = hlim 0 hself
mg′ (asuc _) azero ()
mg′ (asuc _) (asuc _) _ = hself
mg′ (asuc _) (alim _) _ = hself
mg′ (alim _) azero ()
mg′ (alim _) (asuc _) _ = hself
mg′ (alim _) (alim _) _ = hself

lbΩ′ : LgB bΩ
lbΩ′ = (λ {w} {x} {x′} lw e e′ pr → mg′ x x′ pr) , (λ x _ → lgg x)

rp₁′ : Rp.rp {S₀} a₀ bΩ la₀ lbΩ′ H₁ ω₀ p₁ ≡ R₂
rp₁′ = refl

LgIndep : Set
LgIndep = ∀ {a b} (la : Lg a) (lb lb′ : LgB b) (H : EvT.Hist {S₀} a b) c (p : c ⊲[ a ] b) →
          Rel c (Rp.rp {S₀} a b la lb H c p) (Rp.rp {S₀} a b la lb′ H c p)

no-lb-indep : ¬ LgIndep
no-lb-indep I with I la₀ lbΩ lbΩ′ H₁ ω₀ p₁
... | inj₁ e = R-ne e
... | inj₂ (inj₁ (v , q)) = R₁⋬R₂ q
... | inj₂ (inj₂ (v , q)) = R₂⋬R₁ q

WkRel : Set
WkRel = ∀ {a b} (la : Lg a) (lb : LgB b) (lb′ : LgB (hs b)) (H : EvT.Hist {S₀} a b) c (p : c ⊲[ a ] b) →
        Rel c (Rp.rp {S₀} a (hs b) la lb′ (map (WkSuc.wkE a b la lb) H) c (hsuc p)) (Rp.rp {S₀} a b la lb H c p)

no-wk : ¬ WkRel
no-wk I with I la₀ lbΩ lbΩ′ H₁ ω₀ p₁
... | inj₁ e = R-ne (sym e)
... | inj₂ (inj₁ (v , q)) = R₂⋬R₁ q
... | inj₂ (inj₂ (v , q)) = R₁⋬R₂ q

-- 正对照: 合法证明不变, 重放不变
wk-ctl : Rp.rp {S₀} a₀ (hs bΩ) la₀ lbΩ (map (WkSuc.wkE a₀ bΩ la₀ lbΩ) H₁) ω₀ (hsuc p₁) ≡ R₁
wk-ctl = WkSuc.wk-suc a₀ bΩ la₀ lbΩ H₁ ω₀ p₁
```
