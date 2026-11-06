# lΩ 层号上的留/坍缩: 裸坐标推出分离子, 带路径一步归到子层

> 不含记号. Fable 5.1, 2026-11-05 (第四轮自选). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 不改任何已有文件. 导入 [HtTowerTy](HtTowerTy.lagda.md), [LFReTy](LFReTy.lagda.md) (`LH`, `Lv`, `lvl`), [TySupIf](TySupIf.lagda.md) (只用 `Dc`), [TySupC](TySupC.lagda.md) (只用 `ofC`). 不导入收尾中的 `NegTySup*`; 分离子 `Sep` 的三行定义照 `NegTySupSel` 在 `S⊥` 上重写.
>
> **为什么选这一步.** 本轮两路攻击 (`LeanFb`, `TySup`) 的剩余缺口都落在 "跨级 / 含函数的层号" 上; 带类型折叠 (`Fab3Typed` 402 行, `TySup` 504 行) 是目前最短的写法, 它到 ψ₀Λ 只差一件事: `TySup` 接手清单第 1 条, 把实例从可数层号 (`HB S⊥`) 推到 `LFReTy` 的 `lΩ` 层号. 那里种类的位置经 Ω-分支的坐标 $c$, 留/坍缩的决定要比较两个坐标. 作者担心闭项写出来没有意义, 除非树自己能指出下一步. 本篇不去写那个实例, 而是先问树: **在 `lΩ` 层号上, 决定能不能写在 `Lv` 现有的种类上?** 答案是定理: 不能 (§3, 推出分离子); 能的形状也是定理: 坐标带着同一界之下的路径进来时, 一步归到子层 (§4). 两条合起来, 把两路攻击共同的墙在带类型折叠的语言里说成一句: **`lΩ k g` 的种类 `(inj₂ c , κ)` 的坐标 $c$ 是裸的; 任何按层号正确的留/坍缩都要它带路径.** 这不是接口怎么写的问题, 是 `LFReTy.Lv` 这个定义本身的性质 (§5 讨论; 改不改定义由作者定).
>
> **结果.**
>
> 1. **`irr` (定理).** 层号 `LH` 上的裸字面位置 `_⊑ᴸ_` (自反, 经后继, 经 ℕ-极限的分量, 经 `lΩ` 的任一坐标) 反对称 (`anti`), 所以 `ls i ⊑ᴸ i` 不可能. 这一条只用 `LH` 的构造子, 不要合法性.
> 2. **`exact→Sep` (定理, 无条件).** 取层号 $X_1=$ `lΩ lz (λ c → ls (ofC c))` (读 $\Omega_{\Omega_1}$ 的形状: 坐标 $c$ 是可数层号, 分支是第 $c+1$ 层; 判断), 目标 $t_1=$ `ofC t₀`, $t_0=\lim_n 0$. 对每个可数高度 $c$, 种类 `κ c = (inj₂ c , inj₂ tt)` 是 "第 $c$ 层的新种类", 层号 `lvl X₁ (κ c)` 字面是 `ofC c` (`refl`). 若对一切 $c$ 都有一个决定 `Dc`, 且决定**精确** (`Exact`: 留 ⇒ 层号严格在目标下; 同层 ⇒ 层号就是目标; 在上 ⇒ 所报的层就是种类的层号且目标严格在它下面), 则分离子 `Sep`: 对一切 $\alpha$, $\alpha$ 全假或 $a_\alpha\neq t_0$. `Sep` 在 Agda 里证不出 (同 `NegTySupSel.pt-sep`, `Fab2SLsNeg.Sep₂` 的档). 证明不要外延: 只用 `ll` 的单射与 `irr`.
> 3. **`exact₂` (前提实例).** 精确的决定不是空前提: `lΩ lz (λ _ → ls lz)` 上 (分支不依赖坐标) 一律同层, 精确. 可数层号上的实例 `TySupC.decC` 的前两条由 `NegTySupC.ok-ICd` 给出; 第三条的 "目标严格在所报的层之下" 只在字面上看得出 (`pick` 的 "在上" 只在 $t$ 到 `hs i` 的路径至少两步时报, 所以 $t\neq i$; 作为位置 `hs t ⊲ i` 本篇未证, 判断). 所以被否定的恰是 "分支依赖坐标的 `lΩ` 层号" 这一种情形, 而那正是 $\Omega_{\Omega_1}$ 以上一切层号的形状.
> 4. **`om-step` (定理, 构造).** 目标经坐标 $c$, 种类经坐标 $c'$, 两者在同一合法世界的同一合法界 $L$ 之下 ($c\lhd L$, $c'\lhd L$), 层号函数 $g$ 在 $\lhd$ 下单调 ($a\lhd b\Rightarrow g\,a\sqsubseteq g\,b$), 则有一个坐标 $d\in\{c,c'\}$ 使目标与种类的层号都在子层 $g\,d$ 之下: 决定归到子层, 不再经 `lΩ`. 这就是 `cmpB` 的 `hLim` 子句搬到层号上; 新用到的是 $g$ 的单调, 它的形状与 `LgB` 的 Ω-子句相同 (树侧的要求, 不读记号).
>
> **对纲领与目标.** 纲领 3 (壁垒): 这是壁垒在 "层号经 Ω-分支" 处的具体形状: 两个坐标没有字面公共上界就不能比, 比了就推出分离子; 本篇把它落到 `Lv` 的种类上. 目标 (让树自足): 本篇是 "用否定定理划出不能有的字段" 的一例 (AGENTS 最佳实践): 下一步定义的 `lΩ` 种类不能只带裸的 $c$; 正面形状由 `om-step` 给出 (带路径, 归子层). 它没有写出 ψ₀Λ 的闭项; 它说的是任何走带类型折叠到 ψ₀Λ 的闭项必须先改哪一个字段.
>
> **翻译账.** 无新结点, 无接口. `_⊑ᴸ_` 的四个构造子逐一对应 `LH` 的四个构造子 (树侧); `Exact` 是 `NegTySupIf.Ok` 加 "在上严格" (树侧的律, 不读记号); $g$ 的单调形状抄自 `LgB` (树侧). 读法 "$X_1$ 读 $\Omega_{\Omega_1}$" 是判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Fab4LOm where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv; lvl)
open import OCF.Align.TySupIf using (Dc; keep; same; above)
open import OCF.Align.TySupC using (ofC)
```

## §1 层号上的裸字面位置

`a ⊑ᴸ b`: $a$ 是 $b$ 的字面子层号. 经 `lΩ` 时走任一坐标 (裸, 不带界). 严格 `i ⊏ᴸ X` 是 `ls i ⊑ᴸ X` (同 `TySupC` 的 `_⊏ᶜ_`).

```agda
infix 4 _⊑ᴸ_ _⊏ᴸ_
data _⊑ᴸ_ : LH → LH → Set where
  ⊑self : ∀ {a} → a ⊑ᴸ a
  ⊑suc  : ∀ {a b} → a ⊑ᴸ b → a ⊑ᴸ ls b
  ⊑lim  : ∀ {a f} n → a ⊑ᴸ f n → a ⊑ᴸ ll f
  ⊑om   : ∀ {a k g} c → a ⊑ᴸ g c → a ⊑ᴸ lΩ k g

_⊏ᴸ_ : LH → LH → Set
i ⊏ᴸ X = ls i ⊑ᴸ X

⊑ᴸ-tr : ∀ {a b c} → a ⊑ᴸ b → b ⊑ᴸ c → a ⊑ᴸ c
⊑ᴸ-tr p ⊑self = p
⊑ᴸ-tr p (⊑suc q) = ⊑suc (⊑ᴸ-tr p q)
⊑ᴸ-tr p (⊑lim n q) = ⊑lim n (⊑ᴸ-tr p q)
⊑ᴸ-tr p (⊑om c q) = ⊑om c (⊑ᴸ-tr p q)
```

**反对称与不自反 (定理).** 对 $i$ 结构归纳: $a\sqsubseteq i$ 且 $i\sqsubseteq a$ 推出 $a\equiv i$; 于是 `ls i ⊑ᴸ i` 推出 `ls i ≡ i`, 而后者按构造子不可能. 只用 `LH` 的构造子, 不要合法性, 不要外延.

```agda
ls-inj : ∀ {a b} → ls a ≡ ls b → a ≡ b
ls-inj refl = refl

ls≢ : ∀ i → ls i ≡ i → ⊥
ls≢ lz ()
ls≢ (ls j) e = ls≢ j (ls-inj e)
ls≢ (ll f) ()
ls≢ (lΩ k g) ()

anti : ∀ i a → a ⊑ᴸ i → i ⊑ᴸ a → a ≡ i
anti lz a ⊑self q = refl
anti (ls j) a ⊑self q = refl
anti (ls j) a (⊑suc p) q = ⊥-elim (ls≢ j (anti j (ls j) (⊑ᴸ-tr q p) (⊑suc ⊑self)))
anti (ll f) a ⊑self q = refl
anti (ll f) a (⊑lim n p) q =
  trans (anti (f n) a p (subst (λ x → x ⊑ᴸ a) e q)) (sym e)
  where e = anti (f n) (ll f) (⊑ᴸ-tr q p) (⊑lim n ⊑self)
anti (lΩ k g) a ⊑self q = refl
anti (lΩ k g) a (⊑om c p) q =
  trans (anti (g c) a p (subst (λ x → x ⊑ᴸ a) e q)) (sym e)
  where e = anti (g c) (lΩ k g) (⊑ᴸ-tr q p) (⊑om c ⊑self)

irr : ∀ i → i ⊏ᴸ i → ⊥
irr i h = ls≢ i (anti i (ls i) h (⊑suc ⊑self))
```

## §2 精确的决定

`Dc Lv _⊏ᴸ_ _⊑ᴸ_ X t κ` 是 `TySupIf` 的三种结果 (留 / 同层 / 在上), 层号集取 `LH`, 种类结构取 `Lv`. `Exact`: `NegTySupIf.Ok` 的三条, 在上一条加 "目标严格在所报的层之下" (`TySupC.pick` 的 "在上" 只在 $t$ 到 `hs i` 的路径至少两步时报; 可数层号的实例是否字面满足这一条, 本篇未证, 判断).

```agda
Exact : ∀ {X t} (κ : K (Lv X)) → Dc Lv _⊏ᴸ_ _⊑ᴸ_ X t κ → Set
Exact {X} {t} κ (keep _ _) = lvl X κ ⊏ᴸ t
Exact {X} {t} κ (same _) = lvl X κ ≡ t
Exact {X} {t} κ (above i _ _ _) = (i ≡ lvl X κ) × (t ⊏ᴸ i)
```

## §3 裸坐标上的精确决定推出分离子

分离子照 `NegTySupSel` 在 `S⊥` 上写: $a_\alpha=\lim_n[\alpha\,n]$, $t_0=\lim_n 0$.

```agda
bit : Bool → HB S⊥
bit true = hs hz
bit false = hz

aα : (ℕ → Bool) → HB S⊥
aα α = hl (λ n → bit (α n))

t₀ : HB S⊥
t₀ = hl (λ _ → hz)

Sep : Set
Sep = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (aα α ≡ t₀)
```

层号 $X_1$: 坐标是可数高度 $c$, 分支是层号 $c+1$ (`ls (ofC c)`), 所以每个分支都有自己的新种类 `κ c`, 其层号字面是 `ofC c`. 目标 $t_1$ 是 $t_0$ 读成的层号, 经坐标 $t_0$ 在 $X_1$ 之下.

```agda
G : HB S⊥ → LH
G c = ls (ofC c)

X₁ : LH
X₁ = lΩ lz G

κ : HB S⊥ → K (Lv X₁)
κ c = inj₂ c , inj₂ tt

lv-κ : ∀ c → lvl X₁ (κ c) ≡ ofC c
lv-κ c = refl

t₁ : LH
t₁ = ofC t₀

pt₁ : t₁ ⊑ᴸ X₁
pt₁ = ⊑om t₀ (⊑suc ⊑self)
```

**定理.** 对一切 $c$ 有精确的决定, 则分离子. 同层给出 `ofC (aα α) ≡ ofC t₀`, 由 `ll` 单射逐分量得 $\alpha\,n$ 全假; 留与在上都给出层号严格在目标下或上, 与 "层号就是目标" 矛盾 (`irr`).

```agda
ll-inj : ∀ {f g} → ll f ≡ ll g → f ≡ g
ll-inj refl = refl

bitz : ∀ b → ofC (bit b) ≡ lz → b ≡ false
bitz false _ = refl
bitz true ()

exact→Sep : (d : ∀ c → Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₁ t₁ (κ c)) → (∀ c → Exact (κ c) (d c)) → Sep
exact→Sep d ex α = go (d (aα α)) (ex (aα α))
  where
  go : (x : Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₁ t₁ (κ (aα α))) → Exact (κ (aα α)) x →
       (∀ n → α n ≡ false) ⊎ ¬ (aα α ≡ t₀)
  go (same _) e = inj₁ (λ n → bitz (α n) (cong (λ h → h n) (ll-inj e)))
  go (keep _ _) lt = inj₂ (λ e → irr t₁ (subst (λ x → x ⊏ᴸ t₁) (cong ofC e) lt))
  go (above i _ _ _) (ei , lt) = inj₂ (λ e → irr t₁ (subst (λ x → t₁ ⊏ᴸ x) (trans ei (cong ofC e)) lt))
```

**前提实例 (精确的决定可满足).** 分支不依赖坐标的 `lΩ` 层号上, 一律同层就是精确的.

```agda
X₂ : LH
X₂ = lΩ lz (λ _ → ls lz)

κ₂ : HB S⊥ → K (Lv X₂)
κ₂ c = inj₂ c , inj₂ tt

dec₂ : ∀ c → Dc Lv _⊏ᴸ_ _⊑ᴸ_ X₂ lz (κ₂ c)
dec₂ c = same (λ h → h)

exact₂ : ∀ c → Exact (κ₂ c) (dec₂ c)
exact₂ c = refl
```

## §4 带路径: 一步归到子层

目标经坐标 $c$ ($t\sqsubseteq g\,c$), 种类的层号经坐标 $c'$ ($i\sqsubseteq g\,c'$), 两个坐标在同一合法世界的同一合法界 $L$ 之下. 由 `cmpB` 得 $c'\lhd c$ 或 $c\lhd c'$, 再由 $g$ 的单调把一方搬到另一方的子层: 目标与种类的层号同在一个 $g\,d$ 之下, 决定归到子层 $g\,d$, 不再经 `lΩ`. 这是 `cmpB` 的 `hLim` 子句在层号上的样子; 对照 §3: 少了路径 $c'\lhd L$ 就推出分离子.

```agda
om-step : ∀ {k} (g : HB (Lv k) → LH) {w : Wd (Lv k)} {L c c′ t i} →
  c ⊲[ w ] L → c′ ⊲[ w ] L → LgW (Lv k) w → LgB L →
  (∀ {a b} → a ⊲[ w ] b → g a ⊑ᴸ g b) →
  t ⊑ᴸ g c → i ⊑ᴸ g c′ → Σ (HB (Lv k)) (λ d → (t ⊑ᴸ g d) × (i ⊑ᴸ g d))
om-step g p p′ lw lL mo qt qi with cmpB p p′ lw lL
... | inj₁ c′c = _ , qt , ⊑ᴸ-tr qi (mo c′c)
... | inj₂ cc′ = _ , ⊑ᴸ-tr qt (mo cc′) , qi
```

## §5 这两条定理对下一步定义说了什么 (判断)

把 `TySup` 推到 `lΩ` 层号, 折叠对 `hΩ κ′ g′` 递归时遇到的种类 `κ′ = (inj₂ c′ , κ)` 只带裸的 $c'$; 目标的路径 `t ⊑ X` 经 `hLim e` 时带着 $c_t\lhd b$ ($b$ 是世界里 $\Omega_{k+1}$ 的界). §3 说: 没有 $c'\lhd b$ 就不能精确地决定. §4 说: 有了就能. 所以 $c'$ 的路径必须来自**输入高度本身**. 本篇看到三种写法, 都未走通 (判断, 不是否定; 每条都给出卡在哪):

1. **层号带界.** `lΩ k W g` 的坐标限制在 $W$ 的界之下. 但这样的层号读作 $\sup_{c<b} g\,c$, 共尾度是 $b$ 的共尾度, 不再是 $\Omega_{k+1}$: 它是另一个序数, 不是 $\Omega_{\Omega_1}$. 值变了.
2. **高度带位置 (在世界里的高度).** 对高度加一个谓词 "每个种类的坐标在 $W$ 的界之下", 折叠对它递归. 但 $\Omega_{k+1}$-结点的分支 `g′ : HB (Lv k) → HB` 对一切坐标都有值, 界之外的分支没有谓词; 而链 (`chain`) 恰恰要在界之外取分支 ($b\boxplus d_n$ 越过 $b$). 谓词要么对界外的分支无话可说 (折叠无法递归), 要么把分支限制在界内 (链无法步进).
3. **分支依赖证据.** `hΩ κ : ((c : E κ) → Bd κ c w → HB) → HB`, 树以世界为下标. 链的每一点要把输入搬到更大的世界, 而更大的世界有更多坐标需要分支, 小世界的树给不出.

三条合起来 (判断): 在 `lΩ` 层号上, "坐标要带路径" 与 "链要越过界" 是同一个字段上的两个要求. 这就是两路攻击 (`LeanFb` 的 "级 ≥ 2 与含函数层号的拷贝有损", `FabLFReGen`/`Fab2SLs` 的 C6 "层的一半") 在带类型折叠里的样子. 未被否定的出口 (判断): 让链点自带路径 (链的第 $n$ 点 $d_n$ 与界 $b\boxplus d_n$ 之间有字面路径 `⊞-fst`), 即在**折叠的输出**上记录路径而不是在输入上要求路径; 这要求输出类型从 `HB (Lv t)` 变成 "带路径的高度", 回灌不再是恒等. 本篇没有写.

## 结论 (按档)

- **[定理]** `_⊑ᴸ_`, `⊑ᴸ-tr`, `ls≢`, `anti`, `irr`; `Exact`; `exact→Sep` (无条件, 不用外延); `exact₂` (前提实例); `om-step` (构造).
- **[判断]** $X_1$ 读 $\Omega_{\Omega_1}$; `TySupC.decC` 满足 `Exact` 的第三条 (前两条是 `NegTySupC.ok-ICd` 的定理); §5 的三种写法未走通与出口.
- **只否定什么.** 只否定: 在 `LFReTy.Lv` 现有的 `lΩ` 种类 (坐标裸) 上, 对分支依赖坐标的层号, 按层号精确的留/坍缩决定 (对一切坐标) 构造地存在. **不否定**: 带公共上界的决定 (`om-step` 是构造); 不按 "对一切坐标" 陈述的折叠 (只在实际访问的坐标上决定); 改 `lΩ` 的字段 (§5 第 1 条到出口). 本篇没有关闭任何路线.
