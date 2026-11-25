# 真实链点上到达换基行的块与嵌入码
编译定理，不读记号，形状档：`YiBCReach` 那一格的块 `yₑ` 在 `Domain⁺` 里（`yₑ-in`，码 `em tt (old omega)`），way 行交下的整棵嵌入树是码对（`cell-emb`）；但现行 `seen` 不是按这个码换基（`seen≠code`，编译否定）。
同步对象整个是 `Ok⊕`、`rbO` 形（地板 `tw 1`），所以它偏移里沿任意路径降到的每个 ℕ 极限结点上 way 行嵌入码对得码对，每个 Ω 形状结点的 schema 地板是 `tw 1`（`way-sync`、`schema-sync`）；孩子 `a₁ d`（d 是变量，含一切链点）的证据见 `ev-chain`、`rb-chain`，地板一段见 `ev-tw`；现行链从第 1 个点起都是 ℕ 极限（`Feed.chain-L`、`chain-lim`），这种点的顶层显式实例在 `Lim`（`route-lim`、`way-lim`、`row-lim`、`first-lim`）。
不否定什么：不涉及值；"到达 seen 的块只来自 Ω 树分支、部分和、way 嵌入与码树的子块" 是判断；真实链点上 seen 在哪些结点被触发未查。`Feed.L-one` 照搬 `YiRKChain.L₁` 的证明（`l-node`）。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEMChain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiBSRead using (omega)
open import OCF.Lean.YiEMRead
open import OCF.Lean.YiTBRow using (h₁; nat)
open import OCF.Lean.YiRKCell using (IsL; isL)
open import OCF.Lean.YiRKChain using (a₁; l-node; module Real)
open import OCF.Lean.YiBCCover using (ℓₛ; oₛ; rbₛ; gₛ; rb⊑)
open import OCF.Lean.YiBCReach using (G; S₁; yₑ; oω; one)
open import OCF.Lean.YiBSReadNeg using (Hd; hd; hl; hΩ)
```

## `YiBCReach` 那一格（ω 代替链点）

```agda
yₑ-in : Domain⁺ S₁ zero yₑ
yₑ-in = em tt (old omega) , refl
```

`cell-emb` 在下面 `Lim` 之后（取 f = nat）。

现行 `BS.ψ` 在这一格走的 `seen`（`old omega` 的换基）与按 `yₑ` 的码换基（`fold⁺` 取 `em tt (old omega)`）不是同一棵树，对一切 Ok 与底（`seen≠code`）：观察第 1 个部分和的第 0 项的第 0 项的头。

```agda
el : ∀ {S} → ℕ → T S → T S
el n (lim f a) = f n
el n t         = t

obs : ∀ {j} → Tr⁺ j → Hd
obs t = hd (el 0 (el 0 (el 1 (proj₁ t))))

obs-seen : (oj : Ok (G 0)) (β : Tr⁺ (G 0)) → obs (seen S₁ (G 0) oj (lift (tw 1) one) β zero) ≡ hl
obs-seen oj β = refl

obs-code : (oj : Ok (G 0)) (β : Tr⁺ (G 0)) → obs (fold⁺ S₁ zero (em tt (old omega)) (G 0) oj (lift (tw 1) one) β) ≡ hΩ
obs-code oj β = refl

-- perf: 不用 with（with 抽象 eq 时把两棵树整个规范化，6G 撞墙）。
hl≢hΩ : hl ≡ hΩ → ⊥
hl≢hΩ ()

seen≠code : (oj : Ok (G 0)) (β : Tr⁺ (G 0))
  → seen S₁ (G 0) oj (lift (tw 1) one) β zero ≡ fold⁺ S₁ zero (em tt (old omega)) (G 0) oj (lift (tw 1) one) β → ⊥
seen≠code oj β eq = hl≢hΩ (trans (sym (obs-seen oj β)) (trans (cong obs eq) (obs-code oj β)))
```

## 同步对象的孩子：证据的形状（d 是变量）

偏移是 `↑ (tw 1) (gₛ d)`，地板是 `tw 1`；地板一段（`tw 1` 自身）的证据是以 `tw 0` 为地板的 `Ok⊕`。

```agda
ev-chain : (d : Tr zero) → proj₂ oₛ d
  ≡ Ok⊕ (tw 1) (↑ (tw 1) (gₛ d)) (Ok-tw 1) (OkO↑ (tw 1) (tw 1) (Ok-tw 1) self (gₛ d))
ev-chain d = refl

rb-chain : (d : Tr zero) → proj₂ rbₛ d
  ≡ rbO (tw 1) (↑ (tw 1) (gₛ d)) (rb-tw 1) (Ok-tw 1) (OkO↑ (tw 1) (tw 1) (Ok-tw 1) self (gₛ d))
rb-chain d = refl

ev-tw : (n : ℕ) (c : Tr (tw n)) → proj₂ (Ok-tw (suc n)) c ≡ Ok⊕ (tw n) (↑ (tw n) c) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c)
ev-tw n c = refl
```

同步对象 `ℓₛ = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))` 整个是 `Ok⊕`、`rbO` 形（地板 `tw 1`），所以 `YiEMRead.way-at`、`schema-at` 对它偏移里的每个结点成立（`way-sync`、`schema-sync`）；孩子 `a₁ d` 是 d 处的子偏移。

```agda
obₛ : OkO (tw 1) (↑ (tw 1) (proj₁ (Ωt (tw 1))))
obₛ = OkO↑ (tw 1) (tw 1) (Ok-tw 1) self (proj₁ (Ωt (tw 1)))

way-sync : (g′ : ℕ → L) (w : nd sL g′ ⊑ ↑ (tw 1) (proj₁ (Ωt (tw 1)))) (m n : ℕ) (e : Read⁺ (g′ m))
  → WayIn (tw 1) (g′ m) (g′ n) e
      (way (λ i → tw 1 ⊕ g′ i) (proj₁ (downOk (tw 1 ⊕ ↑ (tw 1) (proj₁ (Ωt (tw 1)))) oₛ (tw 1 ⊕ nd sL g′) (wk (⊕⊑ (tw 1) w)))) m n)
way-sync g′ w = way-at (tw 1) g′ w (Ok-tw 1) obₛ

schema-sync : (k : L) (h : Tr k → L) (w : nd (sΩ k) h ⊑ ↑ (tw 1) (proj₁ (Ωt (tw 1))))
  → proj₁ (rb⊑ (tw 1 ⊕ ↑ (tw 1) (proj₁ (Ωt (tw 1)))) rbₛ (⊕⊑ (tw 1) w))
  ≡ just (schema (tw 1) h (Ok-tw 1) (proj₁ (proj₁ (downO (tw 1) w obₛ))) (proj₂ (downO (tw 1) w obₛ)) (λ _ → refl))
schema-sync k h w = schema-at (tw 1) k h w (rb-tw 1) (Ok-tw 1) obₛ
```

## ℕ 极限链点：顶层的显式实例

`offs n`：顶层第 n 个孩子的偏移；`wᶜ n`：相邻孩子之间的 `⊑` 路由（部分和极限的步进经 `◃→⊑` 读出的 `lift`）。

```agda
module Lim (f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) where
  d : Tr zero
  d = lim f a

  gᶜ : ℕ → L
  gᶜ n = zero ⊕ ↑ zero (f n)

  xs : ℕ → Tr (h₁ d)
  xs = cum (λ n → proj₁ (upz {s = sL} {h = gᶜ} n (Ωt (gᶜ n))))

  offs : ℕ → L
  offs n = zero ⊕ ↑ (h₁ d) (xs n)

  shape-lim : a₁ d ≡ tw 1 ⊕ nd sL offs
  shape-lim = refl

  wᶜ : (n : ℕ) → offs n ⊑ offs (suc n)
  wᶜ n = ⊕⊑ zero (lift (↑ (h₁ d) (xs n)) (↑ (gᶜ (suc n)) (proj₁ (Ωt (gᶜ (suc n))))))

  route-lim : (n : ℕ) → proj₁ (proj₂ oₛ d) n ≡ wk (⊕⊑ (tw 1) (wᶜ n))
  route-lim n = refl

  way-lim : (m n : ℕ) (e : Read⁺ (offs m))
    → WayIn (tw 1) (offs m) (offs n) e (way (λ i → tw 1 ⊕ offs i) (proj₁ (proj₂ oₛ d)) m n)
  way-lim m n e = way-in (tw 1) offs wᶜ m n e

  block-lim : (n : ℕ) → Ωt (tw 1 ⊕ offs n) ≡ read⁺ (tw 1) {offs n} (old omega)
  block-lim n = refl
```

`row-lim`：`Ωt (a₁ d)` 的第一个部分和朝孩子 1 下的目标折时，way 行把孩子 0 的块嵌进孩子 1（同 `YiBCReach.way-row`，对任意证据 r、底与目标）；`first-lim`：嵌进去的树对是码对。

```agda
  x₀ : Tr (a₁ d)
  x₀ = proj₁ (upz {s = sL} {h = λ n → tw 1 ⊕ offs n} 0 (Ωt (tw 1 ⊕ offs 0)))

  row-lim : (r : Rb (a₁ d)) (B : Base (a₁ d)) (j : L) (u : j ≤ tw 1 ⊕ offs 1) (β : Tr⁺ j)
    → BS.ψ (a₁ d) (proj₂ oₛ d) r B j (inc 1 u) β x₀
    ≡ BS.ψ (tw 1 ⊕ offs 1) (proj₂ (proj₂ oₛ d) 1) (proj₂ r 1) (λ i u′ → B i (inc 1 u′)) j u β
        (proj₁ (emb (tw 1 ⊕ offs 1) (proj₂ (proj₂ oₛ d) 1) (self ∙ wk (⊕⊑ (tw 1) (wᶜ 0))) (Ωt (tw 1 ⊕ offs 0))))
  row-lim r B j u β = refl

  first-lim : (o : Ok (tw 1 ⊕ offs 1))
    → emb (tw 1 ⊕ offs 1) o (self ∙ wk (⊕⊑ (tw 1) (wᶜ 0))) (Ωt (tw 1 ⊕ offs 0)) ≡ read⁺ (tw 1) (pre (wᶜ 0) (old omega))
  first-lim o = trans (emb-∙ (tw 1 ⊕ offs 1) o self (⊕⊑ (tw 1) (wᶜ 0)) (Ωt (tw 1 ⊕ offs 0)))
    (emb-pre (tw 1) (wᶜ 0) o (old omega))
```

ω 的那一格是 `Lim` 取 f = nat 的实例；way 行交下的整棵嵌入树是码 `em zero (em tt (old omega))` 的读出。

```agda
module Lω = Lim nat (λ _ → ◃s)

cell-emb : emb (G 1) (proj₂ oω 1) (self ∙ proj₁ oω 0) (Ωt (G 0)) ≡ read⁺ (tw 1) {Lω.offs 1} (em zero (em tt (old omega)))
cell-emb = Lω.first-lim (proj₂ oω 1)
```

现行链（`YiRKChain.Real`，与 `YiSYReduce` 的链逐字相等，`YiBCSync.chain-eq`）从第 1 个点起都是 ℕ 极限（对任意证据 o 与底 B），所以 `Lim` 适用于每个链点。第 1 个点照 `YiRKChain.L₁` 用 `l-node`，封进 `opaque`（C-9）；往后由回灌在 ℕ 极限孩子上的那一行（`feed-L`）。

```agda
module Feed (o : Ok ℓₛ) (B : Base ℓₛ) where
  open Real o B using (feed; chain)

  feed-L : ∀ {t} → IsL t → IsL (feed t)
  feed-L (isL f a) = isL _ _

  opaque
    L-one : IsL (chain 1)
    L-one = l-node _ _ _

  chain-L : (m : ℕ) → IsL (chain (suc m))
  chain-L zero    = L-one
  chain-L (suc m) = feed-L (chain-L m)

  chain-lim : (m : ℕ) → Σ (ℕ → Tr zero) λ f → Σ ((n : ℕ) → zero ⊢ f n ◃ f (suc n)) λ a → chain (suc m) ≡ lim f a
  chain-lim m = go (chain-L m)
    where
    go : ∀ {t : Tr zero} → IsL t → Σ (ℕ → Tr zero) λ f → Σ ((n : ℕ) → zero ⊢ f n ◃ f (suc n)) λ a → t ≡ lim f a
    go (isL f a) = f , a , refl
```
