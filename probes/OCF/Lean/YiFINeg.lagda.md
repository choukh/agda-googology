# 整体接口的对照: 现行折叠与候选对两条律

> 判决: 编译定理, 不读记号. 保留律按证据域陈述 (`KeepLawᶜ K E`): 现行 `kp` 在每个 Ω 形状层号上违反 "孩子里的槽位有字面路径就保留" (`kp-violates`, 域非空: `lit₃`, `flr₁`); `kpᴬ` 在字面地板域上满足 (`lawᴬ`), 在字面路径域上违反 (`kpᴬ-violates`, 即 `AuditDCand.cand` 一格, (C) 的 `kpᶜ` 同格见 `cand`); `kpˢ src` 在来源覆盖的域上满足 (`lawˢ`).
> 回退律: 现行回退行在底值不含结点, 前缀为零时输出不含结点 (`main-nf`, `fb-nf`), 所以不低于任何结点 (`no-node`); 上折回退在 K 保留处输出就是结点 (`lift-node`). 对主线块上任何六条生成的分级关系, 参照上下文在这一点保持余尾 Ω 时 `LowKeep` 不成立 (`main-¬low`, 经 `unkept→¬low`; 否定的是接口上的 `LowKeep`, 不是值).
> 不否定什么: `main-¬low` 的前提 `Gen` 没有在主线块上给出实例 (主线关系 `YiGIRel.R` 多一条 `mc`); 底值含结点 (如默认底 `Ωt j`) 时 `main-nf` 不适用. 抽象前提的实例见 `YiAbsGToy.drop-¬low`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFINeg where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp)
open import OCF.Lean.YiTBRow using (Rb; ψ; nat; h₁)
open import OCF.Lean.YiMTTab using (rbᶻ; ψ₀ᶻ)
open import OCF.Lean.YiVALeaf using (NZ; fall; one; two; w₁)
import OCF.Lean.YiDXFold as DX
open DX using (KeepFn; alt; flr; kpᴬ)
open import OCF.Lean.YiKFKeep using (Org; pvT; kpᶜ)
open import OCF.Lean.YiGIBlock using (blkᵍ; foldᵍ; rowsᵍ; ChTᵍ; upᵍ)
open import OCF.Lean.YiAbsSim using (Val)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow using (module Row)
open import OCF.Lean.YiAbsGNeg using (module Neg)
open import OCF.Lean.YiFIFold
```

## 保留律与证据域

`KeepLawᶜ K E`: 证据域 E 内 K 返回保留. `Lit`: 槽位层号到目标有字面路径, 且路径把槽位层号推到目标的真槽位上 (不是目标自己). `Flr`: 槽位层号字面是第 0 层, 目标非零. `Cov src`: 来源 `src` 在这一格给出这样的路径.

```agda
IsJust IsNothing : {A : Set} → Maybe A → Set
IsJust (just _)    = ⊤
IsJust nothing     = ⊥
IsNothing (just _) = ⊥
IsNothing nothing  = ⊤

IsSlot : ∀ {j} → Pos⁼ j → Set
IsSlot (inj₁ _) = ⊥
IsSlot (inj₂ _) = ⊤

EvDom : Set₁
EvDom = (ℓ : L) → Ok ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Set

KeepLawᶜ : KeepFn → EvDom → Set
KeepLawᶜ K E = (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → E ℓ o p w → IsJust (K ℓ o p w)

Lit : EvDom
Lit ℓ o p {j} w = Σ (at ℓ p ≤ j) λ u → IsSlot (psh u (inj₁ tt))

data NZL : L → Set where
  nzl : ∀ s h → NZL (nd s h)

Flr : EvDom
Flr ℓ o p {j} w = (at ℓ p ≡ zero) × NZL j

Cov : Src → EvDom
Cov src ℓ o p {j} w = Σ (at ℓ p ≤ j) λ u → (src ℓ o p w ≡ just u) × IsSlot (psh u (inj₁ tt))
```

满足的一侧.

```agda
alt-r : ∀ {j X x₀} (m n : Keep j X x₀) → IsJust n → IsJust (alt m n)
alt-r (just _) n i = tt
alt-r nothing  n i = i

keep⁼-just : ∀ {j X} (b : L) (f : Tr b → X) (t : Pos⁼ j) cv e → IsSlot t → IsJust (keep⁼ {j} b f t cv e)
keep⁼-just b f (inj₂ q) cv e i = tt

keepOf-just : ∀ ℓ p {j} (u : at ℓ p ≤ j) → IsSlot (psh u (inj₁ tt)) → IsJust (keepOf ℓ p u)
keepOf-just ℓ p u = keep⁼-just (at ℓ p) (fromBr ℓ p) (psh u (inj₁ tt)) (pshBr u (inj₁ tt)) (pshFirst u (inj₁ tt))

lawˢ : (src : Src) → KeepLawᶜ (kpˢ src) (Cov src)
lawˢ src ℓ o p w (u , eq , i) = alt-r (kp ℓ o p w) _
  (subst (λ m → IsJust (fromSrc ℓ p m)) (sym eq) (keepOf-just ℓ p u i))

flr-just : ∀ (a : L) {X : Set} (f : Tr a → X) (j : L) → a ≡ zero → NZL j → IsJust (flr a f j)
flr-just .zero f .(nd s h) refl (nzl s h) = tt

lawᴬ : KeepLawᶜ kpᴬ Flr
lawᴬ ℓ o p {j} w (e , nz) = alt-r (kp ℓ o p w) _ (flr-just (at ℓ p) (fromBr ℓ p) j e nz)
```

违反的一侧. 现行判定在 Ω 形状层号上, 槽位在孩子 c 里, 目标经指定孩子 c′ 时一律走链 (`kp-drop`, 对一切 k, h, c, c′), 与有没有字面路径无关.

```agda
kp-drop : ∀ k h (o : Ok (nd (sΩ k) h)) c t c′ {j} (v : j ≤ h c′)
  → kp (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ≡ nothing
kp-drop k h o c t c′ v = refl

kp-violates : ∀ k h (o : Ok (nd (sΩ k) h)) c t c′ {j} (v : j ≤ h c′) (E : EvDom)
  → E (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) → KeepLawᶜ kp E → ⊥
kp-violates k h o c t c′ v E ev law = law (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ev
```

域非空的两格, 都在塔第 1 项上. 第一格: 槽位在孩子 1 里, 层号第 0 层, 目标 `h₁ 1` 经孩子 2 (`YiVALeaf.w₁`). 第二格 (`AuditDCand` 的一格, 判定件留档在 `Reports-2026-11-16/attachments`): 槽位在孩子 3 里, 层号 `h₁ 2`, 目标 `h₁ 3` 经孩子 3; 字面路径是 `inc tt self`.

```agda
p₁ : Pos (tw 1)
p₁ = inj₂ (one , inj₂ (inj₂ (tt , inj₁ tt)))

flr₁ : Flr (tw 1) (Ok-tw 1) p₁ w₁
flr₁ = refl , nzl _ _

kp-not-flr : KeepLawᶜ kp Flr → ⊥
kp-not-flr = kp-violates zero h₁ (Ok-tw 1) one _ two (inc tt self) Flr flr₁

three : Tr zero
three = nat 3

p₃ : Pos (tw 1)
p₃ = inj₂ (three , inj₂ (inj₂ (tt , inj₁ tt)))

w₃ : h₁ three ≤ tw 1
w₃ = inc three self

lit₃ : Lit (tw 1) (Ok-tw 1) p₃ w₃
lit₃ = inc tt self , tt

kp-not-lit : KeepLawᶜ kp Lit → ⊥
kp-not-lit = kp-violates zero h₁ (Ok-tw 1) three _ three self Lit lit₃

kpᴬ-violates : KeepLawᶜ kpᴬ Lit → ⊥
kpᴬ-violates law = law (tw 1) (Ok-tw 1) p₃ w₃ lit₃

cand : (ot : Org (h₁ three) (tw 1)) → IsNothing (kpᶜ (tw 1) (Ok-tw 1) (pvT 1) p₃ w₃ ot)
cand ot = tt

keepOf₃ : IsJust (keepOf (tw 1) p₃ {h₁ three} (inc tt self))
keepOf₃ = tt
```

非数字孩子上的同类格 (c 是变量, f 是任意合法基本列): 槽位在孩子 c+2 里, 层号 `h₁ (c+1)`, 目标 `h₁ (c+2)` 经同一个孩子或经孩子 c+3; 槽位在 ℕ 极限孩子的第 n 个分量里, 目标是该孩子的层号. 字面路径分别是 `inc tt self`, `inc n self`. 这些格上现行判定与 `kpᴬ` 都走链, `keepOf` 保留.

```agda
module _ (c : Tr zero) where
  pˢ : Pos (tw 1)
  pˢ = inj₂ (suc (suc c) , inj₂ (inj₂ (tt , inj₁ tt)))

  lvlˢ : at (tw 1) pˢ ≡ h₁ (suc c)
  lvlˢ = refl

  wˢ wˢ′ : h₁ (suc (suc c)) ≤ tw 1
  wˢ  = inc (suc (suc c)) self
  wˢ′ = inc (suc (suc (suc c))) (inc tt self)

  litˢ : Lit (tw 1) (Ok-tw 1) pˢ wˢ
  litˢ = inc tt self , tt

  litˢ′ : Lit (tw 1) (Ok-tw 1) pˢ wˢ′
  litˢ′ = inc tt self , tt

  kpᴬ-dropˢ : IsNothing (kpᴬ (tw 1) (Ok-tw 1) pˢ wˢ)
  kpᴬ-dropˢ = tt

  kpᴬ-dropˢ′ : IsNothing (kpᴬ (tw 1) (Ok-tw 1) pˢ wˢ′)
  kpᴬ-dropˢ′ = tt

  keepOfˢ : IsJust (keepOf (tw 1) pˢ {h₁ (suc (suc c))} (inc tt self))
  keepOfˢ = tt

module _ (f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) (n : ℕ) where
  pᴸ : Pos (tw 1)
  pᴸ = inj₂ (lim f a , inj₂ (inj₂ (n , inj₁ tt)))

  lvlᴸ : at (tw 1) pᴸ ≡ h₁ (f n)
  lvlᴸ = refl

  wᴸ : h₁ (lim f a) ≤ tw 1
  wᴸ = inc (lim f a) self

  litᴸ : Lit (tw 1) (Ok-tw 1) pᴸ wᴸ
  litᴸ = inc n self , tt

  kp-dropᴸ : IsNothing (kp (tw 1) (Ok-tw 1) pᴸ wᴸ)
  kp-dropᴸ = tt

  keepOfᴸ : IsJust (keepOf (tw 1) pᴸ {h₁ (lim f a)} (inc n self))
  keepOfᴸ = tt
```

## 回退律

`NF`: 只由零, 后继, ℕ 极限生成 (不含结点与嵌入), 沿第一位置序向下封闭, 所以不低于任何结点.

```agda
data NF {S : Sg} : T S → Set where
  nz : NF zero
  ns : ∀ {x} → NF x → NF (suc x)
  nl : ∀ {f a} → (∀ n → NF (f n)) → NF (lim f a)

nf-down : ∀ {S} {x t : T S} → Lt S x t → NF t → NF x
nf-down ◃s        (ns n) = n
nf-down (◃l n)    (nl f) = f n
nf-down (◃t d d′) n      = nf-down d (nf-down d′ n)

nf-ι : ∀ j (y : Tr zero) → NF (ι j y)
nf-ι j zero      = nz
nf-ι j (suc y)   = ns (nf-ι j y)
nf-ι j (lim f a) = nl (λ n → nf-ι j (f n))

nf+ : ∀ {S} (b : T S) {y : T S} → NF b → NF y → NF (b + y)
nf+ b nb nz     = nb
nf+ b nb (ns n) = ns (nf+ b nb n)
nf+ b nb (nl f) = nl (λ n → nf+ b nb (f n))

nf⊞ : ∀ {j} (β : Tr⁺ j) (z : Tr⁺ zero) → NF (proj₁ β) → NF (proj₁ (β ⊞ z))
nf⊞ {j} β z nβ = nf+ (proj₁ β) nβ (nf-ι j (proj₁ z))

no-node : ∀ {S} {q : P S} {G : B S q → T S} {t : T S} → (Ω q G ≡ t) ⊎ Lt S (Ω q G) t → NF t → ⊥
no-node (inj₁ refl) ()
no-node (inj₂ d) n with nf-down d n
... | ()
```

现行回退行 (开关 `false`, 表缺项): 前缀为零时输出是 `β ⊞ (y 折到第 0 层)`, 不含结点. 主线的 `YiTBRow.ψ` 在塔第 1 项上的同一事实由 `YiVALeaf.fall` 搬来.

```agda
fb-nf : ∀ (K : KeepFn) k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′)
  (β : Tr⁺ j) c y e → NF (proj₁ β)
  → NF (proj₁ (DX.Fold.ψ K false (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β (up zero c y e)))
fb-nf K k h o rc B j c′ v β c y e nβ =
  nf⊞ β (DX.Fold.ψ K false (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y) nβ

main-nf : ∀ {c c′} → NZ c → NZ c′ → (o : Ok (tw 1)) (B : Base (tw 1)) (j : L) (v : j ≤ h₁ c′) (β : Tr⁺ j)
  (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y) → NF (proj₁ β)
  → NF (proj₁ (ψ (tw 1) o (rbᶻ (tw 1)) B j (inc c′ v) β (up zero c y e)))
main-nf {c = c} nc nc′ o B j v β y e nβ =
  subst (λ t → NF (proj₁ t)) (sym (fall nc nc′ o B j v β zero y e)) (nf⊞ β (ψ₀ᶻ (h₁ c) (proj₂ o c) y) nβ)
```

上折回退 (开关 `true`): 孩子材料是结点 `Ω p g`, K 在搬到本层的槽位上保留时, 输出是目标层槽位上的结点, 分支是各分支材料朝同一目标的回退折叠.

```agda
lift-node : ∀ (K : KeepFn) k h (o : Ok (nd (sΩ k) h)) (rc : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′)
  (β : Tr⁺ j) x c (p : Pos (h c)) (g : Br (h c) p → Tr (h c)) e q cv eq
  → K (nd (sΩ k) h) o (mv (down stop c) p) (inc c′ v) ≡ just (q , cv , eq)
  → Σ (Br j q → Tr j) λ G →
      Ω q G ≡ proj₁ (DX.Fold.ψ K true (nd (sΩ k) h) o ((λ _ _ → nothing) , rc) B j (inc c′ v) β (up x c (Ω p g) e))
lift-node K k h o rc B j c′ v β x c p g e q cv eq kq = _ , node-eq _ q cv eq _ _ kq
```

## 接口上的否定

对主线块与现行折叠上的任何分级关系 (`Graded`, 参照系统任意): 目标层的关系由六条规则生成, 参照上下文在嵌入 `up zero c y` 处保持余尾 Ω, 则 `LowKeep` 不成立. 用 `YiAbsGNeg.Inv.unkept→¬low`, "含结点" 取 "不是 `NF`".

```agda
module MainNeg {𝕋 : Ref} {𝕍 : Val} (𝔾 : Graded blkᵍ foldᵍ rowsᵍ 𝕋 𝕍) (𝔻 : Doms blkᵍ foldᵍ) where
  private
    module W = Laws 𝔾 𝔻
    module Rw = Row 𝔾 𝔻
    module Ng = Neg 𝔾 𝔻

  no-up : ∀ {j} {x : Tr j} (c : CH j) (y : ChTᵍ j c) → NF (upᵍ x c y) → ⊥
  no-up c (y , e) ()

  main-¬low : ∀ {c c′} → NZ c → NZ c′ → (o : Ok (tw 1)) (B : Base (tw 1)) (j : L) (v : j ≤ h₁ c′) (β : Tr⁺ j)
    (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y) → NF (proj₁ β)
    → Rw.Gen j → (κ : W.T)
    → (∀ {s} → W.C0 s → W.CΩ s κ → ⊥) → (∀ {s} → W.C1 s → W.CΩ s κ → ⊥) → (∀ {s} → W.Cω s → W.CΩ s κ → ⊥)
    → (Kc : W.Cx (tw 1) j) → W.Gb (tw 1) (o , rbᶻ (tw 1) , B) → W.Wl (inc c′ v) → W.Bd (o , rbᶻ (tw 1) , B) (inc c′ v) β Kc
    → ∀ {a} → W.Gx (tw 1) (up zero c y e) → W.R (tw 1) a (up zero c y e) → W.CΩ (W.app Kc a) κ
    → W.LowKeep → ⊥
  main-¬low {c′ = c′} nc nc′ o B j v β y e nβ G κ d0 d1 dω Kc gb wl bd gx r cΩ =
    Ng.Inv.unkept→¬low G κ (λ t → NF t → ⊥) d0 d1 dω
      (λ p g ()) (λ hx d n → hx (nf-down d n)) (λ c y′ _ _ _ → no-up c y′)
      (o , rbᶻ (tw 1) , B) (inc c′ v) β Kc gb wl bd gx r cΩ
      (λ no → no (main-nf nc nc′ o B j v β y e nβ))
```
