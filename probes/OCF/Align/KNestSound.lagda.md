# 嵌套 `nκ` (四): 带下标的关系, 任意深度归结为一步

> 不含记号. 入口 [KNest](KNest.lagda.md). 把 [KNestAdm](KNestAdm.lagda.md) 的领先量做成关系的**下标**, 不取树的世界:
>
> - **关系** `x ⊑⟨ α , α′ ⟩ x′`. 下标 $(\alpha,\alpha')$ 只由 `κᴬ` 读; `⨾`, `nl`, `nw` 两边透明, 不动下标 (所以 `KNestAdm.lower-left` 不碍事). `loᴬ` 把 `KValTree` 的 `lo` 档整个搬进来 (不含 `nκ` 的部分, 结合律、极限、`ni` 都在那里).
> - **`κᴬ`**: 树世界对 $(V,V')$ 被下标支配 ($\mathrm{Adm}(V,V';\alpha,\alpha')$); 分支在**同一个关系**里比, 层 $c\le c'$ 的一对分支的下标就是 $(c,c')$. 所以嵌套到任意深度, 不分档.
> - **语义** `OutLeᴬ α α′`: `KValSound.OutLe` 的上下文换成 `Cxᴬ` = `KNestInv.Cxᴵ` (状态值可比, 两条单边不变量, 路径一致) 加 $\mathrm{Adm}(\alpha,\alpha';\ell,\ell')$.
>
> **定理** (`sndᴬ`): 只要单个 `nκ` 的一步 `KStepᴬ` 成立 (分支的前提是**语义的** `OutLeᴬ c c′`, 见 §3 的精确类型), 关系对一切深度可靠. 一次结构归纳, `κᴬ` 那一格把分支的推导递归地交给自己. 其余每一步的上下文推进是 `nextᴬ` (`Cxᴵ` 定义性地推进, Adm 由 `adm-adv` 推进).
>
> **覆盖** (`nest-rel`, 定理, 无条件): 嵌套族 $\mathrm{nest}_k$ ($\mathrm{nest}_0=1$, $\mathrm{nest}_{k+1}=\mathrm{n}\kappa(\lambda\_.\,\mathrm{nest}_k)$, 内层树世界跟着层走) 对一切 $k$ 都在关系里; `KNestNeg.uκ` 就是 $\mathrm{nest}_1$, 外层 $\mathrm{n}\kappa\,u_\kappa$ 是 $\mathrm{nest}_2$. 对照: `KNestNeg.¬crit` 说以 `KMono` 为前提的规则推不出它. **与反例相容**: `nest-diag 1` 给出 `uκ 1 ⊑⟨ 1 , 2 ⟩ uκ 2`, 它只在 $\mathrm{Adm}(1,2;\ell,\ell')$ 的上下文里断言单调, 反例的上下文没有这一条 (`KNestAdm.¬adm-cex`).
>
> **包含式的入口** (`contain`): 树世界 $V'\le V$ 时, `OutLeᴬ V V′` 推出不带下标的单调 (上下文只要 `Cxᴵ`): Adm 由 `adm-cont` 从字面路径 $V\to W\to\ell$ 给出.
>
> **`KStepᴬ` 是参数, 没有证.** 它是否成立是本组的未决问题 (判断: 成立, 证法要首对齐, 见入口 §3). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KNestSound where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; _⊞_)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nκ; nw; sum; pt; sum-fst; Lg-sum)
import OCF.Align.SumOneClosed as F
open import OCF.Align.BrwMidZero using (sum-toA)
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree using (Bk; lo; _⊑[_]_; V0)
open import OCF.Align.KValSem using (CohY; cdA; coh⊕; coh₁; ac₁; κ₀; val; toV0)
open import OCF.Align.KValSound using (Sd; W; lW; ll; act; Ok; hx; c0; c1; Rn; Ob; cx; snd-lo)
open import OCF.Align.KNestInv using (ℓ; Cxᴵ; cxᴵ; cLᴵ; cRᴵ; vleᴵ; nextᴵ; iU; iL; hℓ-inv)
open import OCF.Align.KNestAdm using (Adm; adm-adv; adm-cont)
```

## §1 关系

```agda
infix 4 _⊑⟨_,_⟩_
data _⊑⟨_,_⟩_ : ∀ {V V′} → D one V → A → A → D one V′ → Set where
  n0ᴬ  : ∀ {α α′ V V′} {x : D one V′} → n0 {W = V} ⊑⟨ α , α′ ⟩ x
  n1ᴬ  : ∀ {α α′ V V′} → n1 {W = V} ⊑⟨ α , α′ ⟩ n1 {W = V′}
  ⨾ᴬ   : ∀ {α α′ V V′} {x y : D one V} {x′ y′ : D one V′} → x ⊑⟨ α , α′ ⟩ x′ → y ⊑⟨ α , α′ ⟩ y′ → (x ⨾ y) ⊑⟨ α , α′ ⟩ (x′ ⨾ y′)
  nlᴬ  : ∀ {α α′ V V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} → (∀ n → d n ⊑⟨ α , α′ ⟩ d′ n) → nl d ⊑⟨ α , α′ ⟩ nl d′
  nwˡᴬ : ∀ {α α′ V₀ V V′} {p : V₀ ⊲ V} {x : D one V₀} {x′ : D one V′} → x ⊑⟨ α , α′ ⟩ x′ → nw p x ⊑⟨ α , α′ ⟩ x′
  nwʳᴬ : ∀ {α α′ V₀ V V′} {p : V₀ ⊲ V′} {x : D one V} {x′ : D one V₀} → x ⊑⟨ α , α′ ⟩ x′ → x ⊑⟨ α , α′ ⟩ nw p x′
  loᴬ  : ∀ {α α′ V V′} {x : D one V} {x′ : D one V′} → x ⊑[ lo ] x′ → x ⊑⟨ α , α′ ⟩ x′
  κᴬ   : ∀ {α α′ V V′ zz zz′} {u : Bk V} {u′ : Bk V′} → Adm V V′ α α′ →
         (∀ {c c′} (p : V ⊲ c) (p′ : V ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u p l ⊑⟨ c , c′ ⟩ u p′ l′) →
         (∀ {c c′} (p : V′ ⊲ c) (p′ : V′ ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u′ p l ⊑⟨ c , c′ ⟩ u′ p′ l′) →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → u p l ⊑⟨ c , c′ ⟩ u′ p′ l′) →
         nκ zz u ⊑⟨ α , α′ ⟩ nκ zz′ u′
```

## §2 语义与上下文推进

```agda
record Cxᴬ (α α′ : A) (s s′ : Sd) (Y : F.St (W s)) (Y′ : F.St (W s′)) : Set where
  constructor cxᴬ
  field
    ci : Cxᴵ s s′ Y Y′
    ad : Adm α α′ (ℓ Y) (ℓ Y′)
open Cxᴬ public

OutLeᴬ : A → A → ∀ {V V′} → D one V → D one V′ → Set
OutLeᴬ α α′ {V} {V′} x x′ = ∀ (s s′ : Sd) → Ok s s′ → ∀ (q : V ⊲ W s) (q′ : V′ ⊲ W s′) w w′ Y Y′ → Cxᴬ α α′ s s′ Y Y′ →
                            ∀ c c′ → c ≤ c′ → Ob s c x q w Y ≤ Ob s′ c′ x′ q′ w′ Y′

adm-wk : ∀ {α α′ ℓ₁ ℓ ℓ′ ℓ′₁} → ℓ₁ ≤ ℓ → ℓ′ ≤ ℓ′₁ → Adm α α′ ℓ ℓ′ → Adm α α′ ℓ₁ ℓ′₁
adm-wk h h′ (δ , a , b) = δ , ≤-trans h a , ≤-trans b h′

-- 回灌层加上一段第 0 层的输出
adv-sum : ∀ {α α′ ℓ₀ ℓ₀′ W W′} (δ : D azero W) (δ′ : D azero W′) → Adm α α′ ℓ₀ ℓ₀′ → V0 δ ≤ V0 δ′ → Adm α α′ (sum ℓ₀ δ) (sum ℓ₀′ δ′)
adv-sum {ℓ₀ = ℓ₀} {ℓ₀′} δ δ′ a h = adm-wk (proj₁ (sum-toA ℓ₀ δ)) (proj₂ (sum-toA ℓ₀′ δ′)) (adm-adv a h)

nextᴬ : ∀ {α α′ s s′} → Ok s s′ → ∀ {V V′} {x : D one V} {x′ : D one V′} {q q′ w w′ Y Y′} →
        (∀ c c′ → c ≤ c′ → Ob s c x q w Y ≤ Ob s′ c′ x′ q′ w′ Y′) → Cxᴬ α α′ s s′ Y Y′ →
        Cxᴬ α α′ s s′ (Y F.⊕ Rn s x q w Y) (Y′ F.⊕ Rn s′ x′ q′ w′ Y′)
nextᴬ {s = s} {s′} o {x = x} {x′} {q} {q′} {w} {w′} {Y} {Y′} O (cxᴬ ci ad) =
  cxᴬ (nextᴵ Δ Δ′ ci (coh⊕ (cLᴵ ci) cD) (coh⊕ (cRᴵ ci) cD′) (O _ _ (vleᴵ ci))) (adv-sum δ δ′ ad (toV0 δ δ′ le))
  where
  Δ = Rn s x q w Y
  Δ′ = Rn s′ x′ q′ w′ Y′
  cD = coh₁ x q (lW s) (ll s) (act s) w Y (c0 o) (cLᴵ ci)
  cD′ = coh₁ x′ q′ (lW s′) (ll s′) (act s′) w′ Y′ (c1 o) (cRᴵ ci)
  δ = F.yc Δ (inj₁ (z⊲ (W s))) tt
  δ′ = F.yc Δ′ (inj₁ (z⊲ (W s′))) tt
  le : val δ ≤ val δ′
  le = ≤-trans (cdA cD _ (inj₁ (κ₀ (ll s))) azero) (≤-trans (O azero azero z≤) (cdA cD′ (inj₁ (κ₀ (ll s′))) _ azero))
```

## §3 单个 `nκ` 的一步 (参数) 与可靠性

`SX u u′`: 分支在语义上相关, 层 $c\le c'$ 的一对的下标是 $(c,c')$. `KStepᴬ`: 树世界被下标支配、分支语义相关 ⇒ 两个 `nκ` 语义相关.

```agda
SX : ∀ {V V′} → Bk V → Bk V′ → Set
SX {V} {V′} u u′ = ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → OutLeᴬ c c′ (u p l) (u′ p′ l′)

KStepᴬ : Set
KStepᴬ = ∀ {α α′ V V′ zz zz′} {u : Bk V} {u′ : Bk V′} → Adm V V′ α α′ → SX u u → SX u′ u′ → SX u u′ →
         OutLeᴬ α α′ (nκ zz u) (nκ zz′ u′)

sndᴬ : KStepᴬ → ∀ {α α′ V V′} {x : D one V} {x′ : D one V′} → x ⊑⟨ α , α′ ⟩ x′ → OutLeᴬ α α′ x x′
sndᴬ ks n0ᴬ s s′ o q q′ w w′ Y Y′ k c c′ cb = ≤-trans cb (⊲→≤ (sum-fst c′ _))
sndᴬ ks n1ᴬ s s′ o q q′ w w′ Y Y′ k c c′ cb =
  hx o C.self C.self (lW s) (lW s′) w w′ Y Y′ _ _ (cLᴵ (ci k)) (cRᴵ (ci k)) (vleᴵ (ci k)) c c′ cb
sndᴬ ks (⨾ᴬ hx′ hy) s s′ o q q′ w w′ Y Y′ k c c′ cb =
  sndᴬ ks hy s s′ o q q′ _ _ _ _ (nextᴬ o Hx k) _ _ (Hx c c′ cb)
  where Hx = sndᴬ ks hx′ s s′ o q q′ w w′ Y Y′ k
sndᴬ ks (nlᴬ {d = d} {d′} h) s s′ o q q′ w w′ Y Y′ k c c′ cb = l≤ (λ n → ≤l n (proj₁ (go n)))
  where
  P = λ n → F.Rpt ac₁ d q (lW s) (ll s) (act s) w Y n
  P′ = λ n → F.Rpt ac₁ d′ q′ (lW s′) (ll s′) (act s′) w′ Y′ n
  go : ∀ n → (pt c (λ m → F.yc (Rn s (d m) q (proj₁ (P m)) (proj₂ (P m))) (inj₁ (κ₀ (ll s))) tt) n ≤
              pt c′ (λ m → F.yc (Rn s′ (d′ m) q′ (proj₁ (P′ m)) (proj₂ (P′ m))) (inj₁ (κ₀ (ll s′))) tt) n) ×
             Cxᴬ _ _ s s′ (proj₂ (P n)) (proj₂ (P′ n))
  go zero = cb , k
  go (suc n) = let (gb , gk) = go n
                   H = sndᴬ ks (h n) s s′ o q q′ _ _ _ _ gk
               in H _ _ gb , nextᴬ o H gk
sndᴬ ks (nwˡᴬ {p = p} h) s s′ o q q′ = sndᴬ ks h s s′ o (⊲-tr p q) q′
sndᴬ ks (nwʳᴬ {p = p} h) s s′ o q q′ = sndᴬ ks h s s′ o q (⊲-tr p q′)
sndᴬ ks (loᴬ h) s s′ o q q′ w w′ Y Y′ k =
  snd-lo h s s′ o q q′ w w′ Y Y′ (cx (cLᴵ (ci k)) (cRᴵ (ci k)) (vleᴵ (ci k)) tt)
sndᴬ ks (κᴬ a mu mu′ cr) =
  ks a (λ p p′ l l′ le → sndᴬ ks (mu p p′ l l′ le)) (λ p p′ l l′ le → sndᴬ ks (mu′ p p′ l l′ le))
       (λ p p′ l l′ le → sndᴬ ks (cr p p′ l l′ le))
```

## §4 覆盖: 任意深度的嵌套族

```agda
nest : ℕ → ∀ {c} → D one c
nest zero = n1
nest (suc k) = nκ tt (λ _ _ → nest k)

adm-self : ∀ a a′ → Adm a a′ a a′
adm-self a a′ = azero , ≤-refl a , ≤-refl a′

-- 树世界就是下标: 对一切 c, c′ (不要 c ≤ c′)
nest-diag : ∀ k {c c′} → nest k {c} ⊑⟨ c , c′ ⟩ nest k {c′}
nest-diag zero = n1ᴬ
nest-diag (suc k) = κᴬ (adm-self _ _) (λ _ _ _ _ _ → nest-diag k) (λ _ _ _ _ _ → nest-diag k) (λ _ _ _ _ _ → nest-diag k)

nest-rel : ∀ k {V V′ α α′} → Adm V V′ α α′ → nest k {V} ⊑⟨ α , α′ ⟩ nest k {V′}
nest-rel zero a = n1ᴬ
nest-rel (suc k) a = κᴬ a (λ _ _ _ _ _ → nest-diag k) (λ _ _ _ _ _ → nest-diag k) (λ _ _ _ _ _ → nest-diag k)

-- 条件推论: 一步成立, 则一切深度的嵌套族在被支配的上下文里单调
nest-mono : KStepᴬ → ∀ k {V V′ α α′} → Adm V V′ α α′ → OutLeᴬ α α′ (nest k {V}) (nest k {V′})
nest-mono ks k a = sndᴬ ks (nest-rel k a)
```

## §5 包含式的入口: 不带下标的单调

树世界 $V'\le V$, 上下文只要 `Cxᴵ`: Adm 由字面路径 $V\to W\to\ell$ 给出.

```agda
contain : ∀ {V V′} {x : D one V} {x′ : D one V′} → V′ ≤ V → OutLeᴬ V V′ x x′ →
          ∀ (s s′ : Sd) → Ok s s′ → ∀ (q : V ⊲ W s) (q′ : V′ ⊲ W s′) w w′ Y Y′ → Cxᴵ s s′ Y Y′ →
          ∀ c c′ → c ≤ c′ → Ob s c x q w Y ≤ Ob s′ c′ x′ q′ w′ Y′
contain {V} V≤ H s s′ o q q′ w w′ Y Y′ k =
  H s s′ o q q′ w w′ Y Y′ (cxᴬ k (adm-cont (⊲-tr q (sum-fst (W s) (F.z Y))) (Lg-sum (W s) (F.z Y) (lW s)) V≤ hl))
  where
  hl = hℓ-inv s s′ (Cxᴵ.b≤ k) (iU k) (iL k) (cLᴵ k) (cRᴵ k) (vleᴵ k)
```
