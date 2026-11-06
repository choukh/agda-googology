# LeanLv (一): 种类的嵌入, 沿嵌入的连续分支, $\hat\Omega$ 的嵌入

> 不含记号. 入口 [LeanLv](LeanLv.lagda.md), 接口 [LeanLvIf](LeanLvIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 用 `OCF/Lean` 的种类结构重写 [KindLvEmb](../Align/KindLvEmb.lagda.md) (只读参考, 不导入):
>
> - **§1 嵌入的构造.** 恒等 `idE`, `step` 的旧种类 `stepE`, 并的一个分量 `supE i`, 复合 `_∘E_` (同 `KindLvEmb`); 新增: 空结构 `S⊥` 嵌进一切 (`botE`), 并的逐分量嵌入 (`supMap`). 坐标转换都是恒等函数 (坐标类型定义相等).
> - **§2 `nbJ`: 沿嵌入的连续分支** (同 `KindLvEmb.nbJ`), 单调 (`nbJ-mono`), 起点是第一位置 (`nbJ-fst`), 合法由形状给出 (`Lg-nbJ`). 合法性的 $\Omega$-分支用 `bd→` 代替原来的 `lgE→` ([LeanTBase](LeanTBase.lagda.md) 头第 2 条).
> - **§3 $\hat\Omega$ 的嵌入.** `embΩ h : Emb (Lv (ofHB h)) (Lv (ofHB (Ω̂ h)))`, 对 $h$ 的构造子递归; 旧种类的 $\Omega$-结点经 `node` (`nodeMap`, 对 `node` 的同一递归). 于是站的层号之间有嵌入 `emb2 m : Emb (Lv (st 2)) (Lv (st (2+m)))`. 没有沿 `E-lvl` 的搬运: 每一步的坐标类型定义相等.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanLvEmb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanLvIf
open import OCF.Lean.LeanFbSt using (st)
```

## §1 嵌入的构造

```agda
idE : ∀ {S : KS} → Emb S S
idE = record { j = λ κ → κ ; cv = λ e → e ; vc = λ c → c ; cv-vc = λ c → refl ; π = λ w → w ; lgπ = λ l → l
             ; bd→ = λ b → b ; bd← = λ b → b ; pr→ = λ p → p }

stepE : ∀ {S : KS} → Emb S (step S)
stepE = record { j = inj₁ ; cv = λ e → e ; vc = λ c → c ; cv-vc = λ c → refl ; π = proj₁ ; lgπ = proj₁
               ; bd→ = λ b → b ; bd← = λ b → b ; pr→ = λ p → p }

supE : ∀ {I : Set} {F : I → KS} (i : I) → Emb (F i) (sup I F)
supE i = record { j = λ κ → i , κ ; cv = λ e → e ; vc = λ c → c ; cv-vc = λ c → refl ; π = λ w → w i ; lgπ = λ l → l i
                ; bd→ = λ b → b ; bd← = λ b → b ; pr→ = λ p → p }

infixr 9 _∘E_
_∘E_ : ∀ {S₁ S₂ S₃ : KS} → Emb S₂ S₃ → Emb S₁ S₂ → Emb S₁ S₃
F ∘E G = record
  { j = λ κ → j F (j G κ) ; cv = λ e → cv G (cv F e) ; vc = λ c → vc F (vc G c)
  ; cv-vc = λ c → trans (cong (cv G) (cv-vc F (vc G c))) (cv-vc G c)
  ; π = λ w → π G (π F w) ; lgπ = λ l → lgπ G (lgπ F l)
  ; bd→ = λ b → bd→ G (bd→ F b) ; bd← = λ b → bd← F (bd← G b)
  ; pr→ = λ p → pr→ G (pr→ F p) }

module Bot (S : KS) where
  bj : K S⊥ → K S
  bj (() , _)
  bcv : ∀ {κ} → E S (bj κ) → E S⊥ κ
  bcv {() , _}
  bvc : ∀ {κ} → E S⊥ κ → E S (bj κ)
  bvc {() , _}
  bcvvc : ∀ {κ} (c : E S⊥ κ) → bcv {κ} (bvc c) ≡ c
  bcvvc {() , _}
  bbd→ : ∀ {κ e w} → Bd S (bj κ) e w → Bd S⊥ κ (bcv e) (λ ())
  bbd→ {() , _}
  bbd← : ∀ {κ c w} → Bd S⊥ κ c (λ ()) → Bd S (bj κ) (bvc c) w
  bbd← {() , _}
  bpr→ : ∀ {κ e e′ w} → Pr S (bj κ) w e e′ → Pr S⊥ κ (λ ()) (bcv e) (bcv e′)
  bpr→ {() , _}

botE : ∀ {S : KS} → Emb S⊥ S
botE {S} = record { j = bj ; cv = λ {κ} → bcv {κ = κ} ; vc = λ {κ} → bvc {κ = κ} ; cv-vc = λ {κ} → bcvvc {κ = κ} ; π = λ _ () ; lgπ = λ _ ()
              ; bd→ = λ {κ} → bbd→ {κ = κ} ; bd← = λ {κ} → bbd← {κ = κ} ; pr→ = λ {κ} → bpr→ {κ = κ} }
  where open Bot S

supMap : ∀ {I : Set} {F G : I → KS} → (∀ i → Emb (F i) (G i)) → Emb (sup I F) (sup I G)
supMap e = record
  { j = λ κ → proj₁ κ , j (e (proj₁ κ)) (proj₂ κ)
  ; cv = λ {κ} x → cv (e (proj₁ κ)) {proj₂ κ} x ; vc = λ {κ} c → vc (e (proj₁ κ)) {proj₂ κ} c
  ; cv-vc = λ {κ} c → cv-vc (e (proj₁ κ)) {proj₂ κ} c
  ; π = λ w i → π (e i) (w i) ; lgπ = λ l i → lgπ (e i) (l i)
  ; bd→ = λ {κ} b → bd→ (e (proj₁ κ)) {proj₂ κ} b ; bd← = λ {κ} b → bd← (e (proj₁ κ)) {proj₂ κ} b
  ; pr→ = λ {κ} p → pr→ (e (proj₁ κ)) {proj₂ κ} p }
```

## §2 沿嵌入的连续分支

```agda
module _ {S′ S : KS} (Em : Emb S′ S) where
  nbJ : HB S → (HB S′ → HB S → HB S) → HB S′ → HB S
  nbJ b s hz = b
  nbJ b s (hs y) = s y (nbJ b s y)
  nbJ b s (hl f) = hl (λ n → nbJ b s (f n))
  nbJ b s (hΩ κ h) = hΩ (j Em κ) (λ e → nbJ b s (h (cv Em e)))

  module _ {b : HB S} {s : HB S′ → HB S → HB S} (fs : ∀ y h {w} → h ⊲[ w ] s y h) where
    nbJ-mono : ∀ {y y′ w} → y ⊲[ π Em w ] y′ → nbJ b s y ⊲[ w ] nbJ b s y′
    nbJ-mono hself = hself
    nbJ-mono (hsuc p) = ⊲ᴮ-tr (nbJ-mono p) (fs _ _)
    nbJ-mono (hlim n p) = hlim n (nbJ-mono p)
    nbJ-mono {y} {w = w} (hLim {g = h} {c = c} bd p) =
      hLim (bd← Em bd) (subst (λ z → nbJ b s y ⊲[ w ] nbJ b s (h z)) (sym (cv-vc Em c)) (nbJ-mono p))

    nbJ-fst : ∀ y {w} → b ⊲[ w ] nbJ b s y
    nbJ-fst hz = hself
    nbJ-fst (hs y) = ⊲ᴮ-tr (nbJ-fst y) (fs _ _)
    nbJ-fst (hl f) = hlim 0 (nbJ-fst (f 0))
    nbJ-fst (hΩ κ h) {w} = hLim (botBd S (j Em κ) w) (nbJ-fst (h (cv Em (bot S (j Em κ)))))

    Lg-nbJ : LgB b → (∀ y h → LgB h → LgB (s y h)) → ∀ y → LgB y → LgB (nbJ b s y)
    Lg-nbJ lb lS hz _ = lb
    Lg-nbJ lb lS (hs y) l = lS y _ (Lg-nbJ lb lS y l)
    Lg-nbJ lb lS (hl f) (st′ , l) = (λ n → nbJ-mono (st′ n)) , (λ n → Lg-nbJ lb lS (f n) (l n))
    Lg-nbJ lb lS (hΩ κ h) (mo , l) =
      (λ lw e e′ p → nbJ-mono (mo (lgπ Em lw) (bd→ Em e) (bd→ Em e′) (pr→ Em p))) ,
      (λ {w} {c} lw e → Lg-nbJ lb lS (h (cv Em c)) (l (lgπ Em lw) (bd→ Em e)))
```

## §3 $\hat\Omega$ 的嵌入

`ΩE`: 层号 `lΩ x h` 与 `lΩ x h′` 的逐分量嵌入 (左分量 `step (Lv x)` 恒等).

```agda
ΩE : ∀ x (h h′ : HB (Lv x) → LH) → (∀ c → Emb (Lv (h c)) (Lv (h′ c))) →
     (i : ⊤ ⊎ HB (Lv x)) → Emb ([ (λ _ → step (Lv x)) , (λ c → Lv (h c)) ]′ i) ([ (λ _ → step (Lv x)) , (λ c → Lv (h′ c)) ]′ i)
ΩE x h h′ m (inj₁ tt) = idE
ΩE x h h′ m (inj₂ c) = m c

ΩMap : ∀ x (h h′ : HB (Lv x) → LH) → (∀ c → Emb (Lv (h c)) (Lv (h′ c))) → Emb (Lv (lΩ x h)) (Lv (lΩ x h′))
ΩMap x h h′ m = supMap (ΩE x h h′ m)

nodeMap : ∀ k (κ : K (Lv k)) (h h′ : E (Lv k) κ → LH) → (∀ e → Emb (Lv (h e)) (Lv (h′ e))) →
          Emb (Lv (node k κ h)) (Lv (node k κ h′))
nodeMap lz (() , _) h h′ m
nodeMap (ls x) (inj₁ κ) h h′ m = nodeMap x κ h h′ m
nodeMap (ls x) (inj₂ tt) h h′ m = ΩMap x h h′ m
nodeMap (ll f) (n , κ) h h′ m = nodeMap (f n) κ h h′ m
nodeMap (lΩ k g) (inj₁ tt , inj₁ κ) h h′ m = nodeMap k κ h h′ m
nodeMap (lΩ k g) (inj₁ tt , inj₂ tt) h h′ m = ΩMap k h h′ m
nodeMap (lΩ k g) (inj₂ c , κ) h h′ m = nodeMap (g c) κ h h′ m

embΩ : (h : HB SL) → Emb (Lv (ofHB h)) (Lv (ofHB (Ω̂ h)))
embΩ hz = botE
embΩ (hs h) = supE {⊤ ⊎ HB (Lv (ofHB h))} {[ (λ _ → step (Lv (ofHB h))) , (λ c → Lv (ofHB (Ω̂ h ⊞ ι (ofHB h) (up c)))) ]′} (inj₁ tt)
embΩ (hl f) = supMap (λ n → embΩ (f n))
embΩ (hΩ (k , inj₂ tt) g) = ΩMap k (λ c → ofHB (g c)) (λ c → ofHB (Ω̂ (g c))) (λ c → embΩ (g c))
embΩ (hΩ (k , inj₁ κ) g) = nodeMap k κ (λ c → ofHB (g c)) (λ c → ofHB (Ω̂ (g c))) (λ c → embΩ (g c))

-- 第 2 站的层号嵌进第 2+m 站的层号
emb2 : ∀ m → Emb (Lv (st 2)) (Lv (st (suc (suc m))))
emb2 zero = idE
emb2 (suc m) = embΩ (tw (suc (suc m))) ∘E emb2 m
```
