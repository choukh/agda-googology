# 候选 (C): 读回来源的证据与保留判定

> 定义候选, 未经作者采纳, 不进主线; 不读记号. 新证据 `Pv ℓ`: 每个 Ω 形状结点 `nd (sΩ k) h` 上, 对孩子 c 给一张来源表 `Org k (h c)`, 记孩子层号里各 Ω 形状结点的下标槽位来自 k 的哪个槽位 (可缺). 保留判定 `kpᶜ` 在 "槽位在孩子里, 目标经下标层侧 (`ink`)" 一行, 原判定走链而来源表有条目 p′ 时, 交给下标层上的判定; 另含 (A) 的字面地板.
> 编译定理: `Pv` 对读回 `Pv↑`、加法 `Pv⊕`、塔与 Λ (`pvT`, `pvΛ`) 有闭项; 原判定保留处新判定给出同一个槽位与换型, 对一切证据 (`keepʳ`, `keep-kpᶜ`); 那一行的形状 `rowC`; Ω 形状孩子里的槽位之间 `rel` 恒缺 (`rel-Ω-no`).
> 不否定什么. 来源表只按构造子读树与槽位, 孩子下标只在 ⊤ 与 ℕ 上比较 (`rel`), Ω 形状的孩子下标不比较. 折叠在 [YiKFFold](YiKFFold.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKFKeep where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Keep; mapK; kp; kp⁼)
open import OCF.Lean.YiDXFold using (alt; flr; kpᴬ)
```

## 证据

`Org k b`: 层号 b 里每个 Ω 形状结点 (下标层 k″) 带一个可缺的函数, 把它的下标槽位 t 送到 k 的槽位, 连同换型与 "第一分支到第一分支". 条目的类型就是 `Keep k …`, 所以不另设记录. `Pv` 与 `Ok` 同形: Ω 形状结点带下标层的 `Pv` 与每个孩子的来源表.

```agda
OrgS : L → Sh → Set
OrgS k sS      = ⊤
OrgS k sL      = ⊤
OrgS k (sΩ k″) = (t : Pos⁼ k″) → Keep k (Br⁼ k″ t) (bz⁼ k″ t)

Org : L → L → Set
Org k zero     = ⊤
Org k (nd s h) = OrgS k s × ((c : Ch s) → Org k (h c))

mutual
  Pv : L → Set
  Pv zero     = ⊤
  Pv (nd s h) = PvS s h × ((c : Ch s) → Pv (h c))

  PvS : (s : Sh) → (Ch s → L) → Set
  PvS sS     h = ⊤
  PvS sL     h = ⊤
  PvS (sΩ k) h = Pv k × ((c : Tr k) → Org k (h c))

orgS-no : (k : L) (s : Sh) → OrgS k s
orgS-no k sS     = tt
orgS-no k sL     = tt
orgS-no k (sΩ _) = λ _ → nothing

org-no : (k b : L) → Org k b
org-no k zero     = tt
org-no k (nd s h) = orgS-no k s , λ c → org-no k (h c)

pv-no : (ℓ : L) → Pv ℓ
pv-no zero          = tt
pv-no (nd sS h)     = tt , λ c → pv-no (h c)
pv-no (nd sL h)     = tt , λ c → pv-no (h c)
pv-no (nd (sΩ k) h) = (pv-no k , λ c → org-no k (h c)) , λ c → pv-no (h c)

org-at : (k b : L) → Org k b → (t : Pos⁼ b) → Keep k (Br⁼ b t) (bz⁼ b t)
org-at k b             ob       (inj₁ _)              = nothing
org-at k (nd (sΩ _) h) (e , _)  (inj₂ (inj₁ t))       = e t
org-at k (nd s h)      (_ , oc) (inj₂ (inj₂ (c , t))) = org-at k (h c) (oc c) t

mutual
  Pv-at : (ℓ : L) → Pv ℓ → (p : Pos ℓ) → Pv (at ℓ p)
  Pv-at (nd s h)      (_ , pc)       (inj₂ (c , t)) = Pv-at⁼ (h c) (pc c) t
  Pv-at (nd (sΩ k) h) ((pk , _) , _) (inj₁ t)       = Pv-at⁼ k pk t

  Pv-at⁼ : (a : L) → Pv a → (t : Pos⁼ a) → Pv (proj₁ (sl⁼ a t))
  Pv-at⁼ a pa (inj₁ _) = pa
  Pv-at⁼ a pa (inj₂ p) = Pv-at a pa p
```

加法: 偏移 b 的结点原样在外, 前缀 a 在叶子; 前缀一段的来源表取全缺 (前缀自己的槽位原判定已经沿路径保留).

```agda
Org⊕ : (k a b : L) → Org k a → Org k b → Org k (a ⊕ b)
Org⊕ k a zero     oa _         = oa
Org⊕ k a (nd s h) oa (e , oc)  = e , λ c → Org⊕ k a (h c) oa (oc c)

Pv⊕ : (a b : L) → Pv a → Pv b → Pv (a ⊕ b)
Pv⊕ a zero          pa _               = pa
Pv⊕ a (nd sS h)     pa (_ , pc)        = tt , λ c → Pv⊕ a (h c) pa (pc c)
Pv⊕ a (nd sL h)     pa (_ , pc)        = tt , λ c → Pv⊕ a (h c) pa (pc c)
Pv⊕ a (nd (sΩ k) h) pa ((pk , og) , pc) =
  (pk , λ c → Org⊕ k a (h c) (org-no k a) (og c)) , λ c → Pv⊕ a (h c) pa (pc c)
```

## 读回的来源

`subK ℓ p t`: 槽位 p 所在层号里的槽位 t (或那一层本身) 也是 ℓ 的槽位, 分支类型逐字相同. `rel ℓ p p₃`: 槽位 p₃ 字面在槽位 p 的层号之内时, 交出它在那一层里的槽位; 孩子下标只在 ⊤ 上直接下行, 在 ℕ 上用 `eqℕ` 比较, Ω 形状的孩子下标不比较 (缺).

```agda
Slot : (j : L) (X : Set) → X → Set
Slot j X x₀ = Σ (Pos j) λ q → Σ (Br j q → X) λ cv → cv (fromBr j q zero) ≡ x₀

Slot⁼ : (j : L) (X : Set) → X → Set
Slot⁼ j X x₀ = Σ (Pos⁼ j) λ q → Σ (Br⁼ j q → X) λ cv → cv (bz⁼ j q) ≡ x₀

mutual
  subK : (ℓ : L) (p : Pos ℓ) (t : Pos⁼ (at ℓ p)) → Slot ℓ (Br⁼ (at ℓ p) t) (bz⁼ (at ℓ p) t)
  subK (nd s h)      (inj₂ (c , t₀)) t =
    inj₂ (c , proj₁ (subK⁼ (h c) t₀ t)) , proj₁ (proj₂ (subK⁼ (h c) t₀ t)) , proj₂ (proj₂ (subK⁼ (h c) t₀ t))
  subK (nd (sΩ k) h) (inj₁ t₀)       t =
    inj₁ (proj₁ (subK⁼ k t₀ t)) , proj₁ (proj₂ (subK⁼ k t₀ t)) , proj₂ (proj₂ (subK⁼ k t₀ t))

  subK⁼ : (a : L) (t₀ : Pos⁼ a) (t : Pos⁼ (proj₁ (sl⁼ a t₀))) → Slot⁼ a (Br⁼ (proj₁ (sl⁼ a t₀)) t) (bz⁼ (proj₁ (sl⁼ a t₀)) t)
  subK⁼ a (inj₁ _) t = t , (λ z → z) , refl
  subK⁼ a (inj₂ p) t = inj₂ (proj₁ (subK a p t)) , proj₁ (proj₂ (subK a p t)) , proj₂ (proj₂ (subK a p t))

eqℕ : (m n : ℕ) → Maybe (m ≡ n)
eqℕ zero    zero    = just refl
eqℕ zero    (suc n) = nothing
eqℕ (suc m) zero    = nothing
eqℕ (suc m) (suc n) with eqℕ m n
... | just refl = just refl
... | nothing   = nothing

mutual
  rel : (ℓ : L) (p p₃ : Pos ℓ) → Keep (at ℓ p) (Br ℓ p₃) (fromBr ℓ p₃ zero)
  rel (nd sS h)     (inj₂ (_ , t₁)) (inj₂ (_ , t₃)) = rel⁼ (h tt) t₁ t₃
  rel (nd sL g)     (inj₂ (m , t₁)) (inj₂ (n , t₃)) = relL g m n (eqℕ m n) t₁ t₃
  rel (nd (sΩ k) h) (inj₂ _)        (inj₂ _)        = nothing
  rel (nd (sΩ k) h) (inj₁ t₁)       (inj₁ t₃)       = rel⁼ k t₁ t₃
  rel (nd (sΩ k) h) (inj₁ _)        (inj₂ _)        = nothing
  rel (nd (sΩ k) h) (inj₂ _)        (inj₁ _)        = nothing

  relL : (g : ℕ → L) (m n : ℕ) → Maybe (m ≡ n) → (t₁ : Pos⁼ (g m)) (t₃ : Pos⁼ (g n))
       → Keep (proj₁ (sl⁼ (g m) t₁)) (Br⁼ (g n) t₃) (bz⁼ (g n) t₃)
  relL g m .m (just refl) t₁ t₃ = rel⁼ (g m) t₁ t₃
  relL g m n  nothing     t₁ t₃ = nothing

  rel⁼ : (a : L) (t₁ t₃ : Pos⁼ a) → Keep (proj₁ (sl⁼ a t₁)) (Br⁼ a t₃) (bz⁼ a t₃)
  rel⁼ a (inj₁ _)  (inj₁ _)  = nothing
  rel⁼ a (inj₁ _)  (inj₂ p₃) = just (p₃ , (λ z → z) , refl)
  rel⁼ a (inj₂ _)  (inj₁ _)  = nothing
  rel⁼ a (inj₂ p₁) (inj₂ p₃) = rel a p₁ p₃
```

`walk k₀ k R y`: 沿树 y 的构造子读出 `↑ k y` 的来源表. `R` 说 k 的槽位是不是 k₀ 的槽位; 结点 `Ω p g` 读回成下标层 `at k p` 的 Ω 形状结点, 它的下标槽位就是 k 的槽位 (`subK`), 交给 `R`; 嵌入 `up x c y` 进孩子层, `R` 限制到孩子 c 的槽位. `Pv↑` 在读回的每个 Ω 形状结点上取 `R = rel k p` (分支 `g (fromBr k p c)` 是具体的树, 逐个读).

```agda
walk : (k₀ k : L) → ((q : Pos k) → Keep k₀ (Br k q) (fromBr k q zero)) → (y : Tr k) → Org k₀ (↑ k y)
walk k₀ k        R zero         = tt
walk k₀ k        R (suc x)      = tt , λ _ → walk k₀ k R x
walk k₀ k        R (lim f _)    = tt , λ n → walk k₀ k R (f n)
walk k₀ k        R (Ω p g)      =
  (λ t → mapK (proj₁ (proj₂ (subK k p t))) (proj₂ (proj₂ (subK k p t))) (R (proj₁ (subK k p t)))) ,
  λ c → walk k₀ k R (g (fromBr k p c))
walk k₀ (nd s h) R (up x c y _) =
  Org⊕ k₀ (↑ (nd s h) x) (↑ (h c) y) (walk k₀ (nd s h) R x) (walk k₀ (h c) (λ q → R (inj₂ (c , inj₂ q))) y)

own : (k : L) (q : Pos k) → Keep k (Br k q) (fromBr k q zero)
own k q = just (q , (λ z → z) , refl)

Pv↑ : (k : L) → Pv k → (y : Tr k) → Pv (↑ k y)
Pv↑ k        pk zero         = tt
Pv↑ k        pk (suc x)      = tt , λ _ → Pv↑ k pk x
Pv↑ k        pk (lim f _)    = tt , λ n → Pv↑ k pk (f n)
Pv↑ k        pk (Ω p g)      =
  (Pv-at k pk p , λ c → walk (at k p) k (rel k p) (g (fromBr k p c))) , λ c → Pv↑ k pk (g (fromBr k p c))
Pv↑ (nd s h) pk (up x c y _) = Pv⊕ (↑ (nd s h) x) (↑ (h c) y) (Pv↑ (nd s h) pk x) (Pv↑ (h c) (proj₂ pk c) y)

pvT : (n : ℕ) → Pv (tw n)
pvT zero    = tt
pvT (suc n) =
  (pvT n , λ c → Org⊕ (tw n) (tw n) (↑ (tw n) c) (org-no (tw n) (tw n)) (walk (tw n) (tw n) (own (tw n)) c)) ,
  λ c → Pv⊕ (tw n) (↑ (tw n) c) (pvT n) (Pv↑ (tw n) (pvT n) c)

pvΛ : Pv Λ
pvΛ = tt , pvT
```

## 保留判定

`kpʳ` 逐行复制 `YiRWFold.kp`, 只在 "Ω 形状, 槽位在孩子 c 里, 目标经下标层侧" 一行多一个退路: 原判定 (沿 `k ≤ h c` 进孩子) 走链而来源表有条目时, 用下标层上的判定 (`bindK`). `kpᶜ` 再加 (A) 的字面地板.

```agda
bindK : ∀ {j k X x₀} → Keep k X x₀ → ((p′ : Pos k) → Keep j (Br k p′) (fromBr k p′ zero)) → Keep j X x₀
bindK (just (p′ , f , e)) F = mapK f e (F p′)
bindK nothing             F = nothing

mutual
  kpʳ : (ℓ : L) → Ok ℓ → Pv ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)
  kpʳ ℓ             o               pv               p              self      = just (p , (λ z → z) , refl)
  kpʳ (nd s h)      (_ , oc)        (_ , pc)         (inj₂ (c , t)) (inu vs)  = kpʳ⁼ (h c) (oc c) (pc c) t (vs c)
  kpʳ (nd (sΩ k) h) ((ok , kh) , oc) ((pk , og) , pc) (inj₂ (c , t)) (ink v)   =
    alt (kpʳ⁼ (h c) (oc c) (pc c) t (v ∙ kh c)) (bindK (org-at k (h c) (og c) t) (λ p′ → kpʳ k ok pk p′ v))
  kpʳ (nd sS h)     (_ , oc)        (_ , pc)         (inj₂ (c , t)) (inc _ v) = kpʳ⁼ (h c) (oc c) (pc c) t v
  kpʳ (nd sL g)     (r , oc)        (_ , pc)         (inj₂ (m , t)) (inc n v) =
    cW (way g r m n) (λ u → mapK (pshBr u t) (pshFirst u t) (kpʳ⁼ (g n) (oc n) (pc n) (psh u t) v))
                     (λ u → kpʳ⁼ (g m) (oc m) (pc m) t (v ∙ u))
  kpʳ (nd (sΩ k) h) _               _                (inj₂ _)       (inc _ _) = nothing
  kpʳ (nd (sΩ k) h) ((ok , _) , _)  ((pk , _) , _)   (inj₁ t)       (ink v)   = kpʳ⁼ k ok pk t v
  kpʳ (nd (sΩ k) h) ((_ , kh) , oc) (_ , pc)         (inj₁ t)       (inc c v) =
    mapK (pshBr (kh c) t) (pshFirst (kh c) t) (kpʳ⁼ (h c) (oc c) (pc c) (psh (kh c) t) v)
  kpʳ (nd (sΩ k) h) ((_ , kh) , oc) (_ , pc)         (inj₁ t)       (inu vs)  =
    mapK (pshBr (kh zero) t) (pshFirst (kh zero) t) (kpʳ⁼ (h zero) (oc zero) (pc zero) (psh (kh zero) t) (vs zero))

  kpʳ⁼ : (a : L) → Ok a → Pv a → (t : Pos⁼ a) → ∀ {j} → j ≤ a → Keep j (Br⁼ a t) (bz⁼ a t)
  kpʳ⁼ a o pv (inj₁ _) w = nothing
  kpʳ⁼ a o pv (inj₂ p) w = kpʳ a o pv p w

```

## 折叠带着走的来源表

`kpʳ` 的那一行只管直接在 `nd (sΩ k) h` 层上的结点. 折叠沿 `ink` 行进入孩子 c 之后, 层号变成 `h c`, 路径变成 `v ∙ kh c`, 父层的来源表不在孩子的 `Pv` 里; 所以折叠另带一张 "朝当前目标 j 的来源表" `ot : Org j ℓ`. 它在 `ink` 行生成 (`dlg`: 孩子 c 的来源表逐条交给下标层上的判定, 得到朝 j 的条目), 进孩子时取分量, 换目标 (回灌, 底) 时清空 (`org-no`). `kpᶜ`: 先 `kpʳ`, 再查 `ot`, 最后 (A) 的字面地板.

```agda
mapOrgS : (k j : L) → ((p′ : Pos k) → Keep j (Br k p′) (fromBr k p′ zero)) → (s : Sh) → OrgS k s → OrgS j s
mapOrgS k j F sS     _ = tt
mapOrgS k j F sL     _ = tt
mapOrgS k j F (sΩ _) e = λ t → bindK (e t) F

mapOrg : (k j : L) → ((p′ : Pos k) → Keep j (Br k p′) (fromBr k p′ zero)) → (b : L) → Org k b → Org j b
mapOrg k j F zero     _        = tt
mapOrg k j F (nd s h) (e , oc) = mapOrgS k j F s e , λ c → mapOrg k j F (h c) (oc c)

altOrgS : (j : L) (s : Sh) → OrgS j s → OrgS j s → OrgS j s
altOrgS j sS     _ _  = tt
altOrgS j sL     _ _  = tt
altOrgS j (sΩ _) e e′ = λ t → alt (e t) (e′ t)

altOrg : (j b : L) → Org j b → Org j b → Org j b
altOrg j zero     _        _          = tt
altOrg j (nd s h) (e , oc) (e′ , oc′) = altOrgS j s e e′ , λ c → altOrg j (h c) (oc c) (oc′ c)

dlg : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (pv : Pv (nd (sΩ k) h)) {j : L} (v : j ≤ k)
    → Org j (nd (sΩ k) h) → (c : Tr k) → Org j (h c)
dlg k h ((ok , _) , _) ((pk , og) , _) {j} v (_ , oc) c =
  altOrg j (h c) (oc c) (mapOrg k j (λ p′ → kpʳ k ok pk p′ v) (h c) (og c))

KeepFnᴾ : Set
KeepFnᴾ = (ℓ : L) → Ok ℓ → Pv ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Org j ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)

kpᶜ : KeepFnᴾ
kpᶜ ℓ o pv p {j} w ot = alt (kpʳ ℓ o pv p w) (alt (org-at j ℓ ot (inj₂ p)) (flr (at ℓ p) (fromBr ℓ p) j))
```

那一行的形状.

```agda
rowC : ∀ k h (o : Ok (nd (sΩ k) h)) (pv : Pv (nd (sΩ k) h)) c t {j} (v : j ≤ k)
  → kpʳ (nd (sΩ k) h) o pv (inj₂ (c , t)) (ink v)
  ≡ alt (kpʳ⁼ (h c) (proj₂ o c) (proj₂ pv c) t (v ∙ proj₂ (proj₁ o) c))
        (bindK (org-at k (h c) (proj₂ (proj₁ pv) c) t) (λ p′ → kpʳ k (proj₁ (proj₁ o)) (proj₁ (proj₁ pv)) p′ v))
rowC k h o pv c t v = refl
```

`rel` 不是 "能保留处都保留": 同一个 Ω 形状孩子里的两个槽位, 即使字面相同, 也没有条目.

```agda
rel-Ω-no : ∀ k h (x y : Σ (Tr k) λ c → Pos⁼ (h c)) → rel (nd (sΩ k) h) (inj₂ x) (inj₂ y) ≡ nothing
rel-Ω-no k h x y = refl
```

## 原有的保留不变

`Ref m m′`: m 保留时 m′ 给出同一个槽位、换型与证明. 对 `kp` 的子句归纳; 新增的退路只在原判定走链时起作用.

```agda
Ref : ∀ {j X x₀} → Keep j X x₀ → Keep j X x₀ → Set
Ref m m′ = ∀ K → m ≡ just K → m′ ≡ just K

ref-map : ∀ {j X Y x₀ y₀} (f : X → Y) (e : f x₀ ≡ y₀) {m m′ : Keep j X x₀} → Ref m m′ → Ref (mapK f e m) (mapK f e m′)
ref-map f e {m = just K₀} r K q rewrite r K₀ refl = q
ref-map f e {m = nothing} r K ()

ref-alt : ∀ {j X x₀} {m m′ n : Keep j X x₀} → Ref m m′ → Ref m (alt m′ n)
ref-alt r K q rewrite r K q = refl

mutual
  keepʳ : (ℓ : L) (o : Ok ℓ) (pv : Pv ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → Ref (kp ℓ o p w) (kpʳ ℓ o pv p w)
  keepʳ ℓ             o               pv               p              self      = λ K q → q
  keepʳ (nd s h)      (_ , oc)        (_ , pc)         (inj₂ (c , t)) (inu vs)  = keepʳ⁼ (h c) (oc c) (pc c) t (vs c)
  keepʳ (nd (sΩ k) h) ((ok , kh) , oc) ((pk , og) , pc) (inj₂ (c , t)) (ink v)   =
    ref-alt (keepʳ⁼ (h c) (oc c) (pc c) t (v ∙ kh c))
  keepʳ (nd sS h)     (_ , oc)        (_ , pc)         (inj₂ (c , t)) (inc _ v) = keepʳ⁼ (h c) (oc c) (pc c) t v
  keepʳ (nd sL g)     (r , oc)        (_ , pc)         (inj₂ (m , t)) (inc n v) =
    cW-ind₂ Ref (way g r m n)
      (λ u → ref-map (pshBr u t) (pshFirst u t) (keepʳ⁼ (g n) (oc n) (pc n) (psh u t) v))
      (λ u → keepʳ⁼ (g m) (oc m) (pc m) t (v ∙ u))
  keepʳ (nd (sΩ k) h) _               _                (inj₂ _)       (inc _ _) = λ K ()
  keepʳ (nd (sΩ k) h) ((ok , _) , _)  ((pk , _) , _)   (inj₁ t)       (ink v)   = keepʳ⁼ k ok pk t v
  keepʳ (nd (sΩ k) h) ((_ , kh) , oc) (_ , pc)         (inj₁ t)       (inc c v) =
    ref-map (pshBr (kh c) t) (pshFirst (kh c) t) (keepʳ⁼ (h c) (oc c) (pc c) (psh (kh c) t) v)
  keepʳ (nd (sΩ k) h) ((_ , kh) , oc) (_ , pc)         (inj₁ t)       (inu vs)  =
    ref-map (pshBr (kh zero) t) (pshFirst (kh zero) t) (keepʳ⁼ (h zero) (oc zero) (pc zero) (psh (kh zero) t) (vs zero))

  keepʳ⁼ : (a : L) (o : Ok a) (pv : Pv a) (t : Pos⁼ a) {j : L} (w : j ≤ a) → Ref (kp⁼ a o t w) (kpʳ⁼ a o pv t w)
  keepʳ⁼ a o pv (inj₁ _) w = λ K ()
  keepʳ⁼ a o pv (inj₂ p) w = keepʳ a o pv p w

keep-kpᶜ : (ℓ : L) (o : Ok ℓ) (pv : Pv ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) (ot : Org j ℓ) → Ref (kp ℓ o p w) (kpᶜ ℓ o pv p w ot)
keep-kpᶜ ℓ o pv p w ot = ref-alt (keepʳ ℓ o pv p w)
```
