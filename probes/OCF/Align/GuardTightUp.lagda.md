# 更高的定义域: 读回, 条件的对角线, 与编译过的障碍

> 不含记号. 结论写在 [GuardTight](GuardTight.lagda.md).
>
> - `rbO`, `F⁺`: 第 1 层的树读回 `LG`, $\psi_1(\Omega_x)$. **定义, 不是好层号的定理.**
> - `GL`, `GoodFeed`, `Diag`: $\psi_0(\Omega_{\Omega_2})=\sup_n\psi_0(\Omega_{u_n})$, $u_0=\Omega_1$, $u_{n+1}=\psi_1(\Omega_{u_n})$ (与 EBO 的基本列逐项一致: `walk s₄`). **`Diag.TΩ₂` 以 `GoodFeed` 为模块参数, 是条件定义.** 模块参数就是 `good-feed`, 它没有证. $u_0,u_1$ 不用条件: `u₀`, `u₁` 是闭项 ($u_1=$ `Lv₅`).
> - `no-WFˢ-Ω⁺`: **编译过的否定. $\Omega_2$ 作为 $\mathbb D_1$ 上的层号没有 `WFˢ`.** 所以 [GuardTightTree](GuardTightTree.lagda.md) 的 `Fold` (比较带对一切表的转移) 不能实例化到 `𝔻ₙ`. 不是工程量. 理由: 上升 $x\mapsto x$ 的路径搬运要穿过分支 $\eta$, 而分支 $\eta$ 的证据在表里没有.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardTightUp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightCum using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; Ordᶜ; Simᴵ; Ω; add; natᴵ; zero; suc; lim; z≅; s⊑)
import OCF.Align.GuardTightCum as Lvl
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
import OCF.Align.GuardTightUni as Uni
private module U = Uni Dom₀
open U using (rb₁; rb-≈₁₁; Good-Ω; Good→WF₁; F; Lv₅; Cf-Lv₅)
open import OCF.Align.GuardTightRd using (module RdIter)
```

## §1 读回

`oŝ c t g` 读成带守卫的闭包 `lc c t g`. 节点 $\Omega_1$ 读成下界 1 的闭包, 输入是 `Ordᴵ` 嵌入的树.

```agda
emO : Ordᴵ → O zero tz
emO zero = o0
emO (suc a) = os (emO a)
emO (lim f s) = ol (λ n → emO (f n))

rbO : ∀ {π} → O (suc zero) π → LG
rbO o0 = zero
rbO (os a) = suc (rbO a)
rbO (ol F′) = lim (λ n → rbO (F′ n))
rbO (oŝ c t g) = lc c (rbO t) (λ η e → rbO (g η e))
rbO (oĉ c z zg o₀ o) = lc c (rbO o₀) (λ η e → rbO (o η e))
rbO (owk w x) = rbO x
rbO (ocv w x) = rbO x
rbO (omk R lk ad z x) = rbO x
rbO (oΩ zero cv h) = lc (suc Lvl.zero) (rbO (h tz (emO (suc Lvl.zero)))) (λ η e → rbO (h tz (emO η)))
rbO (oΩ (suc ()) _ _)
rbO (ocl (suc ()) _ _ _ _)

-- ψ₁(Ω_x): 目标 1 的字面路径 q 与表 E 是输入
F⁺ : (x : LG) → Cfˢ x → Tc x → (E : Ents) → (q : suc zero < x) → Adm (tab E) q → LG
F⁺ x (w , s) tc E q aq = rbO (Fold.ψ x w s tc {π = tz} {ρ = tz} E (Fold.tp q aq) (λ ()) (Ω̇ x tc))
```

## §2 条件的对角线

`GL`: 带全部证书的层号, 外加目标 1 的路径. `GoodFeed`: `F⁺` 把它送回 `GL`. 这是 `good-feed`, **模块参数, 没有证**. 模块 `Diag` 里的一切都是条件定义.

```agda
record GL : Set where
  constructor gl
  field
    lvl  : LG
    cfG  : Cfˢ lvl
    tcG  : Tc lvl
    entG : Ents
    pthG : suc zero < lvl
    admG : Adm (tab entG) pthG
open GL public

feedL : GL → LG
feedL u = F⁺ (lvl u) (cfG u) (tcG u) (entG u) (pthG u) (admG u)

record GoodFeed : Set where
  field
    cfF  : ∀ u → Cfˢ (feedL u)
    tcF  : ∀ u → Tc (feedL u)
    entF : GL → Ents
    pthF : ∀ u → suc zero < feedL u
    admF : ∀ u → Adm (tab (entF u)) (pthF u)

u₀ : GL
u₀ = gl (rb₁ (Ω (suc zero))) (Good→WF₁ (Good-Ω (suc zero)) , rb-≈₁₁ (Lvl.Ω-refl (suc zero))) RdIter.Tc-c
        (∅ (natᴵ 2)) (bra (natᴵ 2) (s⊑ z≅ (suc zero)) Lv.zero) ((natᴵ 2 , refl , zero) , tt)

module Diag (G : GoodFeed) where
  open GoodFeed G
  next : GL → GL
  next u = gl (feedL u) (cfF u) (tcF u) (entF u) (pthF u) (admF u)

  us : ℕ → GL
  us zero = u₀
  us (suc n) = next (us n)

  -- ψ₀(Ω_{Ω₂}). 一个定义, 对 n 没有分情况.
  TΩ₂ : Z
  TΩ₂ = Z.lim (λ n → T₀ (lvl (us n)) (cfG (us n)) (tcG (us n)))
```

## §3 $\Omega_2$ 上没有 `WFˢ`

$x=\Omega+3$, $y=\Omega\cdot2$: `x ⊑ⁿ y` (路径穿过分支 3), 所以 $x$ 严格低于 $y+1$ 的守卫成立. `WFˢ` 要求 `emb x ⊴ emb y`, 也就是路径搬运带对**一切**表的转移. 取分支 3 没有证据的表: 第一支里放不下 $\Omega+2$ (`irr`), 分支里没有证据. 矛盾. 与 [LvKeyStep](LvKeyStep.lagda.md) 的 `no-↑` 同形, 这里是对 `𝔻₁` 的 `Ω⁺` 写的.

```agda
open import OCF.Align.GuardTightNext using (module Up)
open import OCF.Align.GuardTightCum using (_+_; add-≅; Ω-refl)
private
  module Uₙ = Up Dom₀
  module L₁ = Uₙ.L₁
import OCF.Align.GuardTightTab as TabM
private module Tab₁ = TabM Uₙ.NextDom

xΩ x₂ : LG
xΩ = rb₁ (Ω (suc zero))
x₂ = rb₁ (Ω (suc zero) + Ω (suc zero))

zero<3 : zero <ᴵ natᴵ 3
zero<3 = suc (suc zero)

e₃ : suc zero ⊑ᴵ natᴵ 3
e₃ = s⊑ z≅ zero<3

cfΩ : Cfˢ xΩ
cfΩ = Good→WF₁ (Good-Ω (suc zero)) , rb-≈₁₁ (Ω-refl (suc zero))

cf₂ : Cfˢ x₂
cf₂ = Good→WF₁ (U.Good-add {σ = λ q → q} (Good-Ω (suc zero)) (Ω-refl (suc zero)) (Good-Ω (suc zero))) ,
      rb-≈₁₁ (add-≅ {σ = λ q → q} {σ′ = λ q → q} (Ω-refl (suc zero)) (Ω-refl (suc zero)))

x₃′ : LG
x₃′ = suc (suc (suc xΩ))

gx₃ gy : Uₙ.GLv
gx₃ = x₃′ , (WFˢ→WF xΩ (proj₁ cfΩ) , s≈ (s≈ (s≈ (proj₂ cfΩ))))
gy = x₂ , (WFˢ→WF x₂ (proj₁ cf₂) , proj₂ cf₂)

guard : x₃′ ⊑ⁿ x₂
guard r = pre (selfAt (s≈ (s≈ (s≈ (proj₂ cfΩ)))) r) (bra (natᴵ 3) e₃ r)

-- 分支里的 Ω₁ 没有与自身等价的严格前驱
no-self : ∀ {r} → r L₁.≈ Uₙ.emb xΩ → Tab₁.Strict r (Uₙ.emb xΩ) → ⊥
no-self d s = Tab₁.irr (Uₙ.emb xΩ) s (L₁.≈-sym d)

no-WFˢ-Ω⁺ : L₁.WFˢ Uₙ.Ω⁺ → ⊥
no-WFˢ-Ω⁺ (tg , dir , wt , wg) with L₁.⊴p (dir (inj₂ gx₃) (λ ()) (inj₂ gy) (λ ()) guard) L₁.zero
... | L₁.viaᴸ d (L₁.fst L₁.zero) t with d
...   | ()
no-WFˢ-Ω⁺ (tg , dir , wt , wg) | L₁.viaᴸ (L₁.s≈ (L₁.s≈ d′)) (L₁.fst (L₁.suc r)) t =
  no-self (L₁.≈-sym d′) (Tab₁.st⊙ (Tab₁.toCp r) (Tab₁.st-suc (L₁.suc L₁.self)))
no-WFˢ-Ω⁺ (tg , dir , wt , wg) | L₁.viaᴸ d (L₁.bra (inj₁ η) e′ r) t with t (L₁.tab (L₁.∅ (inj₁ zero))) tt
... | (_ , refl , ()) , _
no-WFˢ-Ω⁺ (tg , dir , wt , wg) | L₁.viaᴸ d (L₁.bra (inj₂ _) () r) t
```
