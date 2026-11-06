# UIP 条件下的回灌 (三): 第二级, 世界不压回, 现有的折叠压回

> 不含记号. 入口 [UipFb](UipFb.lagda.md). 第二级的新种类是 `Slot` 在坐标 $2$ (`fin 2`) 处的新种类, 坐标类型 `HB S₂`, $S_2$ = `step S₁` (`UipFbChain.E-κ₃`). 两件事:
>
> 1. **世界侧 (无条件).** 外层世界 $(0,2)$ 里 (`UipFbClosed.w₂`, 相干无条件), 在坐标 $2$ 处用 `raise₀` 接上 $\Omega_{\mathrm{top}}S_1$ (以 `HB S₁` 为坐标的新种类的 $\Omega$-节点), 格 $0\boxplus\Omega_{\mathrm{top}}S_1$ 有界 (`bd-κ₃`), 含新种类节点 (`new-κ₃`). 所以第二级的世界同样不把新节点挡在界外.
> 2. **折叠侧 (无条件).** 以 `HB S₂` 为层的折叠没有; 现有的只有两种种类的折叠 `T⁺` (层 `HB S₁`). 把 `HB S₂` 的高度交给它, 这里用 `TdPlusUni.pr` 那样的投影 `pr₂` ("现有工具下只写得出投影" 是判断): 旧种类原样, 新种类 (坐标 `HB S₁`) 的 $\Omega$-节点只留 $H_0$ 嵌入处的分支, 读成 `κH` 节点. **`Lg-pr₂`**: 合法高度投影成合法高度 (只在一致世界 $((a,\beta),\mathrm{up}\,\beta)$ 里用原高度的合法性, 依据 `TdPlusUni.up-inv`). 于是 `fold₂ = T⁺ ∘ pr₂` 是对一切合法 `HB S₂` 高度的折叠, 合法由形状给出. **`pr₂-top`**: 第二级级顶 $\Omega_{\mathrm{top}}S_1$ 投影后与 `Ω₂ᴴ` 互模拟; **`pr₂-cell`**: 第 1 条那个有界的格投影后也与 `Ω₂ᴴ` 互模拟. 所以 `t₂ = fold₂ (Ωtop S₁)` 与 `T-Ω₂` 是互模拟输入上的同一个折叠 (同 `TdPlusVal.pr-top` 对 `t₊ (k+1)`).
>
> **它说明什么 (定理部分).** 第 1 条与第 2 条同时成立: 世界把第二级的新节点格放进了界 (`bd-κ₃`), 折叠 `fold₂` 仍把级顶压回 $\Omega_2$ (`pr₂-top`). `pr₂` 不读 `Slot` 的世界 (它的合法性只用 $S_2$ 的一致世界). 所以 `pr-top` 那种压回是投影折叠的性质, 与世界族 (`growL′` 或 `raise₀`) 无关. **判断**: 第二级要不被压回, 缺的是以 `HB S₂` 为层的折叠 (三种种类, 或对一切级的折叠), 不是世界, 也不是 `UIPᴴ`.
>
> **范围.** `pr₂-top` 只说 `fold₂` 这一个折叠; 它不否定别的以 `HB S₂` 为层的折叠 (没有写出来的那些). 互模拟输入上 `T⁺` 的值相等是判断 (同 `TdPlusVal`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UipFbTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; κA; κH)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺; Ω₂ᴴ; T-Ω₂)
open import OCF.Align.DiagK3Zero using (_≈_; ≈z; ≈s; ≈l; ≈Ω)
open import OCF.Align.DiagK3One using (NoNew)
open import OCF.Align.TdPlusUni using (up-inv)
open import OCF.Align.TdPlusVal using (≈-trans)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (raise₀)
open import OCF.Align.UipFbChain using (yes-Ω-cell; new-Ωtop)
open import OCF.Align.UipFbClosed using (w₂; lo₂; vz; coh-b₂)
open Slot

S₂ : KS
S₂ = step S₁
```

## §1 世界侧: 第二级的新节点格有界

```agda
v₃ : Cmp w₂
v₃ = raise₀ w₂ lo₂ (vz w₂) (hs (hs hz)) hself (Ωtop S₁)

cell₃ : HB S₂
cell₃ = hz ⊞ Ωtop S₁

bd-κ₃ : Bdᴮ (hs (hs hz) , inj₂ tt) cell₃ (w₂ , v₃)
bd-κ₃ = yes-Ω-cell w₂ lo₂ (vz w₂) (hs hz) hself

new-κ₃ : ¬ NoNew cell₃
new-κ₃ ()

coh-κ₃ : Coh≡ (w₂ , v₃)
coh-κ₃ = coh-b₂ v₃
```

## §2 投影到两种种类

```agda
pr₂ : HB S₂ → Ht
pr₂ hz = hz
pr₂ (hs x) = hs (pr₂ x)
pr₂ (hl f) = hl (λ n → pr₂ (f n))
pr₂ (hΩ (inj₁ κ) g) = hΩ κ (λ c → pr₂ (g c))
pr₂ (hΩ (inj₂ tt) g) = hΩ κH (λ h → pr₂ (g (up h)))

pr₂-mono : ∀ {x y : HB S₂} {a β} → x ⊲[ ((a , β) , up β) ] y → pr₂ x ⊲[ (a , β) ] pr₂ y
pr₂-mono hself = hself
pr₂-mono (hsuc p) = hsuc (pr₂-mono p)
pr₂-mono (hlim n p) = hlim n (pr₂-mono p)
pr₂-mono (hLim {κ = inj₁ κ} e p) = hLim e (pr₂-mono p)
pr₂-mono (hLim {κ = inj₂ tt} e p) with up-inv e
... | h′ , refl , q = hLim {κ = κH} {c = h′} q (pr₂-mono p)

Lg-pr₂ : ∀ x → LgB x → LgB (pr₂ x)
Lg-pr₂ hz l = tt
Lg-pr₂ (hs x) l = Lg-pr₂ x l
Lg-pr₂ (hl f) (st , l) = (λ {w} n → pr₂-mono {a = proj₁ w} {β = proj₂ w} (st n)) , (λ n → Lg-pr₂ (f n) (l n))
Lg-pr₂ (hΩ (inj₁ κ) g) (mo , l) =
  (λ {w} lw e e′ r → pr₂-mono {a = proj₁ w} {β = proj₂ w} (mo {((proj₁ w , proj₂ w) , up (proj₂ w))} (lw , Lg-up (proj₂ w) (proj₂ lw)) e e′ r)) ,
  (λ c lc → Lg-pr₂ (g c) (l c lc))
Lg-pr₂ (hΩ (inj₂ tt) g) (mo , l) =
  (λ {w} lw e e′ r → pr₂-mono {a = proj₁ w} {β = proj₂ w}
     (mo {((proj₁ w , proj₂ w) , up (proj₂ w))} (lw , Lg-up (proj₂ w) (proj₂ lw)) (up-⊲ e) (up-⊲ e′) (up-⊲ r))) ,
  (λ h lh → Lg-pr₂ (g (up h)) (l (up h) (Lg-up h lh)))
```

## §3 现有的第二级折叠, 级顶被压回

```agda
fold₂ : (Λ : HB S₂) → LgB Λ → A
fold₂ Λ lΛ = T⁺ (pr₂ Λ) (Lg-pr₂ Λ lΛ)

Lg-fold₂ : ∀ Λ (lΛ : LgB Λ) → Lg (fold₂ Λ lΛ)
Lg-fold₂ Λ lΛ = Lg-T⁺ (pr₂ Λ) (Lg-pr₂ Λ lΛ)

pr₂-up : ∀ (y : Ht) → pr₂ (up y) ≈ y
pr₂-up hz = ≈z
pr₂-up (hs y) = ≈s (pr₂-up y)
pr₂-up (hl f) = ≈l (λ n → pr₂-up (f n))
pr₂-up (hΩ κ g) = ≈Ω (λ c → pr₂-up (g c))

pr₂-top : pr₂ (Ωtop S₁) ≈ Ω₂ᴴ
pr₂-top = ≈Ω (λ h → pr₂-up (up h))

t₂ : A
t₂ = fold₂ (Ωtop S₁) (Lg-Ωtop S₁)

-- 有界的那个格, 投影后也是 Ω₂
hz⊞ : ∀ {S} (y : HB S) → (hz ⊞ y) ≈ y
hz⊞ hz = ≈z
hz⊞ (hs y) = ≈s (hz⊞ y)
hz⊞ (hl f) = ≈l (λ n → hz⊞ (f n))
hz⊞ (hΩ κ g) = ≈Ω (λ c → hz⊞ (g c))

pr₂-≈ : ∀ {x y : HB S₂} → x ≈ y → pr₂ x ≈ pr₂ y
pr₂-≈ ≈z = ≈z
pr₂-≈ (≈s p) = ≈s (pr₂-≈ p)
pr₂-≈ (≈l p) = ≈l (λ n → pr₂-≈ (p n))
pr₂-≈ (≈Ω {κ = inj₁ κ} p) = ≈Ω (λ c → pr₂-≈ (p c))
pr₂-≈ (≈Ω {κ = inj₂ tt} p) = ≈Ω (λ h → pr₂-≈ (p (up h)))

pr₂-cell : pr₂ cell₃ ≈ Ω₂ᴴ
pr₂-cell = ≈-trans (pr₂-≈ (hz⊞ (Ωtop S₁))) pr₂-top
```
