# NegValX (三): ValC 用到的 "自环只有 `hself`" 等价于 `Cd` 上的 UIP

> 不含记号. 入口 [NegValX](NegValX.lagda.md). 本篇**不依赖**构造一路 ValX 的接口. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [CRw](CRw.lagda.md) (实例 `I₁`, 只为引用 ValC 的 `selfLoop`), [ValCMono](ValCMono.lagda.md) (`selfLoop`, 作正方向), [ValCUip](ValCUip.lagda.md) (`UIPC` 的定义). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. 本篇的定理都以 "某个陈述" 为前提推出另一个陈述 (蕴含式), 不假设 UIP 或函数外延.
>
> **问题.** ValC 的单调定理以 `Cd` 上的 UIP 为前提, 只用在一处: `ValCMono.selfLoop` ($r : k\lhd k$ 字面是 `hself`), 由它得 `sameR` (两次 "同层" 的决定). ValC 的接手清单提出两条去掉前提的出路: "证 `cmpB` 的路径相干性" 与 "两个 `cmpB` 结果同为 `inj₁ (hsuc r)` 时 $r$ 相同". 本篇问: 这些陈述比 UIP 弱吗?
>
> 1. **`loop→K`, `K→uip`, `selfLoop⇔uip` (定理).** "一切 $r : k\lhd k$ 都是 `hself`" (对一切 $k$) 等价于 `Cd` 上的 UIP. 方向 ⇐ 是 ValC 的 `selfLoop`; 方向 ⇒: 由 $e : k\equiv k$ 造 $r_e$ = 沿 $e$ 搬运 `hself`, 一个读回函数 `ρ` (`hself` ↦ `just refl`, 其余 ↦ `nothing`) 把 $r_e$ 送回 `just e`; 所以 $r_e\equiv$ `hself` 推出 $e\equiv$ `refl` (K), K 推出 UIP.
> 2. **`canon→K` (定理).** "对合法的公共上界 $L$, `cmpB` 比较 $k+1\lhd L$ 与 $k\lhd L$ 时, 结果若是 `inj₁ (hsuc r)` 则 $r$ 是 `hself`" (ValC 的第二条出路, 正是 `sameR` 要的) 推出合法 $k$ 处的 K: 取 $L=k+1$, 第一条路径 `hself`, `cmpB` 的第一个子句原样返回第二条路径. 所以这条出路**不比** UIP (在合法树上) 弱.
> 3. **`uip→Kfun` (定理).** `Cd` 上的 UIP 推出函数类型 $\mathbb N\to$ `Cd` 上的 K (对一切 $f$, $f\equiv f$ 的证明都是 `refl`): `hl` 单射, 读回 `pr`. 合法版本 `canon→Kfun`: 只要 $\lim f$ 合法. 这说明前提实质上是关于**函数类型**的相等的, 与 `fe→uipC` 用函数外延给出它一致.
>
> **前提实例.** 1 的两边: UIP 由函数外延给出 (`ValCUip.fe→uipC`, 条件 Funext); 这里的定理是蕴含式, 前提的可满足性就是 UIP 的可满足性. 2 的前提 `Canon` 由 UIP 推出 (`uip→canon`, 经 `selfLoop`), 所以可满足 (条件同上).
>
> **只否定什么.** 只说: 经 `selfLoop`, 或经 "`cmpB` 结果的规范性" 去掉 UIP, 等于证 UIP (在合法树上). **不说**: `Cd` 上的 UIP 在 `--without-K` 下不可证 (那是元定理, 本篇没有模型; 判断: 不用函数外延时, 函数类型上的 K 一般不可证, `uip→Kfun` 说明 UIP 至少有这么强); **不说** ValC 的单调定理需要 UIP (换一种证明, 不经 "两次同层的决定化简成同一个 `same`", 也许不需要; 例如让关系本身吸收沿自环的搬运, 未走通, 没有试).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValXUip where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.ValCUip using (UIPC)
import OCF.Lean.ValCMono as VM
```

## §1 读回

```agda
ρ : ∀ {a b : Cd} → a ⊲ b → Maybe (a ≡ b)
ρ hself = just refl
ρ (hsuc _) = nothing
ρ (hlim _ _) = nothing
ρ (hLim {κ = ()} _ _)

ρ-tr : ∀ {k z : Cd} (e : k ≡ z) → ρ (subst (λ w → k ⊲ w) e hself) ≡ just e
ρ-tr refl = refl

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl
```

## §2 自环只有 `hself` ⟺ UIP

```agda
SelfLoopAt : Cd → Set
SelfLoopAt k = ∀ (r : k ⊲ k) → r ≡ hself

KAt : Cd → Set
KAt k = ∀ (e : k ≡ k) → e ≡ refl

loop→K : ∀ {k} → SelfLoopAt k → KAt k
loop→K {k} sl e = just-inj (trans (sym (ρ-tr e)) (cong ρ (sl (subst (λ w → k ⊲ w) e hself))))

K→uip : (∀ {k} → KAt k) → UIPC
K→uip K e e′ = go e e′
  where
  go : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′
  go e refl = K e

-- 合法树上的版本
K→uipᴸ : ∀ {x} → KAt x → ∀ {y} (e e′ : x ≡ y) → e ≡ e′
K→uipᴸ K e refl = K e

SelfLoop : Set
SelfLoop = ∀ {k} → SelfLoopAt k

-- 正方向: ValC 的 selfLoop (以 UIP 为模块参数)
uip→loop : UIPC → SelfLoop
uip→loop u = VM.selfLoop I₁ u

loop→uip : SelfLoop → UIPC
loop→uip sl = K→uip (loop→K sl)
```

## §3 `cmpB` 结果的规范性 ⟹ 合法树上的 K

`Canon`: 公共上界 $L$ 合法时, 比较 $k+1\lhd L$ 与 $k\lhd L$, 结果若是 `inj₁ (hsuc r)`, 则 $r$ 是 `hself`. 这正是 ValC 的 `sameR` 在第二次 "同层" 决定处要的.

```agda
Canon : Set
Canon = ∀ {k L : Cd} (p : hs k ⊲ L) (q : k ⊲ L) (lL : LgB L) (r : k ⊲ k) →
        cmpB p q tt lL ≡ inj₁ (hsuc r) → r ≡ hself

canon→loop : Canon → ∀ {k} → LgB k → SelfLoopAt k
canon→loop c {k} lk r = c hself (hsuc r) lk r refl

canon→K : Canon → ∀ {k} → LgB k → KAt k
canon→K c lk = loop→K (canon→loop c lk)

canon→uipᴸ : Canon → ∀ {x} → LgB x → ∀ {y} (e e′ : x ≡ y) → e ≡ e′
canon→uipᴸ c lx = K→uipᴸ (canon→K c lx)

-- 前提可满足 (条件: UIP)
uip→canon : UIPC → Canon
uip→canon u p q lL r _ = uip→loop u r
```

## §4 UIP 推出函数类型上的 K

```agda
pr : Cd → (ℕ → Cd)
pr (hl f) = f
pr _ = λ _ → hz

pr-hl : ∀ {f g : ℕ → Cd} (e : f ≡ g) → cong pr (cong hl e) ≡ e
pr-hl refl = refl

KAt→Kfun : ∀ {f : ℕ → Cd} → KAt (hl f) → ∀ (e : f ≡ f) → e ≡ refl
KAt→Kfun K e = trans (sym (pr-hl e)) (cong (λ z → cong pr z) (K (cong hl e)))

uip→Kfun : UIPC → ∀ (f : ℕ → Cd) (e : f ≡ f) → e ≡ refl
uip→Kfun u f e = KAt→Kfun (λ e′ → u e′ refl) e

-- 合法版本: 规范性推出合法序列上函数类型的 K
canon→Kfun : Canon → ∀ {f : ℕ → Cd} → LgB (hl f) → ∀ (e : f ≡ f) → e ≡ refl
canon→Kfun c lf = KAt→Kfun (canon→K c lf)
```

## 结论 (按档)

- **[定理]** `loop→K`, `K→uip`, `loop→uip` (自环只有 `hself` ⟹ `Cd` 上的 UIP); `uip→loop` (反方向, 即 ValC 的 `selfLoop`); `canon→loop`, `canon→K`, `canon→uipᴸ` (`cmpB` 结果的规范性 ⟹ 合法树上的 K 与 UIP); `uip→canon`; `KAt→Kfun`, `uip→Kfun`, `canon→Kfun` (推出函数类型 $\mathbb N\to$ `Cd` 上的 K).
- **[判断]** 不用函数外延时 `Cd` 上的 UIP 在 `--without-K` 下不可证 (元定理, 本篇没有模型). 所以经 `selfLoop` 或 `Canon` 去掉前提**未走通**, 而且这两条出路本身就等于前提. 其他出路 (不经 `sameR` 的证明) 本篇没有试.
