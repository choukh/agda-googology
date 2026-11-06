# 两种种类的单调 (四): 与关系无关的和结构核

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [MonoPort3Gen](MonoPort3Gen.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. 原文导入而不使用的 `MonoPortBridge.smono` 去掉.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY; D)
module OCF.Align.TpPortGen (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtTowerFTree using (n0; n1; _⨾_; nl; nw; sum; pt; sum-fst; ≤rf) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (module At)


module P = At Λ lΛ oΛ

T₀ : P.Tg W hz W
T₀ = P.tg ≤rf t₀ lW

o₀ : P.Df W → D hz W
o₀ Δ = P.yc Δ T₀

infixl 6 _⊕_
_⊕_ : P.St W → P.Df W → P.St W
Y ⊕ Δ = P._⊕⟨_⟩_ Y lW Δ

vY : P.St W → A
vY Y = sum azero (o₀ (P.d Y))

preL : ∀ {ly V} → (ℕ → D ly V) → ℕ → D ly V
preL d zero = n0
preL d (suc k) = preL d k ⨾ d k

preᴰ : (ℕ → P.Df W) → ℕ → P.Df W
preᴰ F zero = P.zeroD
preᴰ F (suc k) = preᴰ F k P.⨾ᴰ F k
```
```agda
record OutLaws : Set₁ where
  field
    _≼_  : P.Df W → P.Df W → Set
    L0   : ∀ {Δ} → P.zeroD ≼ Δ
    L⨾   : ∀ {a b a′ b′} → a ≼ a → a′ ≼ a′ → a ≼ a′ → b ≼ b′ → (a P.⨾ᴰ b) ≼ (a′ P.⨾ᴰ b′)
    Lnl  : ∀ {F F′ : ℕ → P.Df W} → (∀ n → F n ≼ F n) → (∀ n → F′ n ≼ F′ n) → (∀ n → F n ≼ F′ n) → P.nlᴰ F ≼ P.nlᴰ F′
    Ltr  : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
    Lu0ˡ : ∀ {a a′} → a ≼ a′ → (P.zeroD P.⨾ᴰ a) ≼ a′
    Lu0ʳ : ∀ {a a′} → a ≼ a′ → a ≼ (P.zeroD P.⨾ᴰ a′)
    Lu1ˡ : ∀ {a a′} → a ≼ a′ → (a P.⨾ᴰ P.zeroD) ≼ a′
    Lu1ʳ : ∀ {a a′} → a ≼ a′ → a ≼ (a′ P.⨾ᴰ P.zeroD)
    Lasˡ  : ∀ {a b c t} → a ≼ a → b ≼ b → c ≼ c → (a P.⨾ᴰ (b P.⨾ᴰ c)) ≼ t → ((a P.⨾ᴰ b) P.⨾ᴰ c) ≼ t
    Lasˡ′ : ∀ {a b c t} → a ≼ a → b ≼ b → c ≼ c → ((a P.⨾ᴰ b) P.⨾ᴰ c) ≼ t → (a P.⨾ᴰ (b P.⨾ᴰ c)) ≼ t
    Lasʳ  : ∀ {a b c t} → a ≼ a → b ≼ b → c ≼ c → t ≼ ((a P.⨾ᴰ b) P.⨾ᴰ c) → t ≼ (a P.⨾ᴰ (b P.⨾ᴰ c))
    Lasʳ′ : ∀ {a b c t} → a ≼ a → b ≼ b → c ≼ c → t ≼ (a P.⨾ᴰ (b P.⨾ᴰ c)) → t ≼ ((a P.⨾ᴰ b) P.⨾ᴰ c)

-- 部分和与极限两条单列: 结构关系可以不要 Llim
PreLaw LimLaw : OutLaws → Set
PreLaw O = ∀ {a a′} {F F′ : ℕ → P.Df W} → a ≼ a → a′ ≼ a′ → (∀ n → F n ≼ F n) → (∀ n → F′ n ≼ F′ n) →
           a ≼ a′ → (∀ n → F n ≼ F′ n) → ∀ k → (a P.⨾ᴰ preᴰ F k) ≼ (a′ P.⨾ᴰ P.nlᴰ F′)
  where open OutLaws O
LimLaw O = ∀ {a t} {F : ℕ → P.Df W} → a ≼ a → (∀ n → F n ≼ F n) → (∀ k → (a P.⨾ᴰ preᴰ F k) ≼ t) → (a P.⨾ᴰ P.nlᴰ F) ≼ t
  where open OutLaws O
```
```agda
module Core (O : OutLaws) (ly : Ht) (ac : AccY ly) (ll : ly ⊲[ W ] Λ)
  (TW : Set) (tw : TW → Wd₂) (Path : TW → Set) (emb : ∀ {V} → Path V → tw V ≤ʷ W)
  (Cx₀ : D ly W → D ly W → Set) (In₀ : ∀ {V₁ V₂} → D ly (tw V₁) → D ly (tw V₂) → Set) where
  open OutLaws O public

  -- 包成记录, 让隐式参数可由类型推出
  record Cx (w w′ : D ly W) : Set where
    constructor cx
    field ucx : Cx₀ w w′

  record In {V₁ V₂} (x : D ly (tw V₁)) (x′ : D ly (tw V₂)) : Set where
    constructor inn
    field uin : In₀ x x′

  SRel : P.St W → P.St W → Set
  SRel Y Y′ = (vY Y ≤ vY Y′) × (P.d Y ≼ P.d Y′)

  Good : P.St W → Set
  Good Y = P.d Y ≼ P.d Y

  sr : ∀ {Y} → Good Y → SRel Y Y
  sr g = ≤-refl _ , g

  Obs : A → A → P.Df W → P.Df W → Set
  Obs c c′ Δ Δ′ = (sum c (o₀ Δ) ≤ sum c′ (o₀ Δ′)) × (Δ ≼ Δ′)

  G⊕ : ∀ {Y Δ} → Good Y → Δ ≼ Δ → Good (Y ⊕ Δ)
  G⊕ g r = L⨾ g g g r

  S⊕ : ∀ {Y Y′ Δ Δ′} → Good Y → Good Y′ → SRel Y Y′ → Obs (vY Y) (vY Y′) Δ Δ′ → SRel (Y ⊕ Δ) (Y′ ⊕ Δ′)
  S⊕ g g′ s o = proj₁ o , L⨾ g g′ (proj₂ s) (proj₂ o)

  Act : Set
  Act = P.Ig ly W

  Run : Act → ∀ {V} → D ly (tw V) → Path V → D ly W → P.St W → P.Df W
  Run A₀ x q w Y = P.Run ac x (emb q) lW ll A₀ w Y

  HA : Act → Act → Set
  HA A₀ A₁ = ∀ w w′ c c′ Y Y′ → Cx w w′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (A₀ ≤rf lW w Y) (A₁ ≤rf lW w′ Y′)

  I : Set
  I = Σ Act (λ (A₀ : Act) → HA A₀ A₀)

  Hy : I → I → Set
  Hy i j = HA (proj₁ i) (proj₁ j)

  Sem : Act → Act → ∀ {V₁ V₂} → D ly (tw V₁) → D ly (tw V₂) → Set
  Sem i j x x′ = ∀ q q′ w w′ c c′ Y Y′ → Cx w w′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ →
                 Obs c c′ (Run i x q w Y) (Run j x′ q′ w′ Y′)

  rf : ∀ {Aᵢ : Act} {V} {x : D ly (tw V)} → Sem Aᵢ Aᵢ x x → ∀ q w Y → Cx w w → Good Y → Run (Aᵢ) x q w Y ≼ Run (Aᵢ) x q w Y
  rf h q w Y cw g = proj₂ (h q q w w azero azero Y Y cw g g (sr g) z≤)

  -- 部分和走出来的输出, 字面就是各段输出的部分和
  module PreOut (A₀ : Act) {V} (d : ℕ → D ly (tw V)) (q : Path V) (w : D ly W) (Z : P.St W) where
    Rp : ℕ → P.Df W
    Rp k = Run A₀ (preL d k) q w Z
    Ek : ℕ → P.Df W
    Ek k = Run A₀ (d k) q (w ⨾ nw (emb q) (preL d k)) (Z ⊕ Rp k)
    O≡ : ∀ k → Rp k ≡ preᴰ Ek k
    O≡ zero = refl
    O≡ (suc k) = cong (λ t → t P.⨾ᴰ Ek k) (O≡ k)
```
```agda
  record CxLaws : Set where
    field
      cxL   : ∀ {w w′} → Cx w w′ → Cx w w
      cxR   : ∀ {w w′} → Cx w w′ → Cx w′ w′
      cx⨾   : ∀ {V₁ V₂ w w′} {x : D ly (tw V₁)} {x′ : D ly (tw V₂)} (q : Path V₁) (q′ : Path V₂) → Cx w w′ → In x x′ → Cx (w ⨾ nw (emb q) x) (w′ ⨾ nw (emb q′) x′)
      cx0ˡ  : ∀ {V w w′} (q : Path V) → Cx w w′ → Cx (w ⨾ nw (emb q) (n0 {W = tw V})) w′
      cx0ʳ  : ∀ {V w w′} (q : Path V) → Cx w w′ → Cx w (w′ ⨾ nw (emb q) (n0 {W = tw V}))
      cxas  : ∀ {V w} {x y : D ly (tw V)} (q : Path V) → Cx w w → In x x → In y y → Cx (w ⨾ nw (emb q) (x ⨾ y)) ((w ⨾ nw (emb q) x) ⨾ nw (emb q) y)
      cxas′ : ∀ {V w} {x y : D ly (tw V)} (q : Path V) → Cx w w → In x x → In y y → Cx ((w ⨾ nw (emb q) x) ⨾ nw (emb q) y) (w ⨾ nw (emb q) (x ⨾ y))
      cxpre : ∀ {V₁ V₂ w R} {d : ℕ → D ly (tw V₁)} {e : D ly (tw V₂)} (q : Path V₁) (q′ : Path V₂) n →
              Cx (w ⨾ nw (emb q) (preL d n)) R → In (d n) e → Cx (w ⨾ nw (emb q) (preL d (suc n))) (R ⨾ nw (emb q′) e)
      cxlim : ∀ {V L w} {d : ℕ → D ly (tw V)} (q : Path V) n →
              Cx L (w ⨾ nw (emb q) (preL d n)) → In (d n) (d n) → Cx (L ⨾ nw (emb q) (d n)) (w ⨾ nw (emb q) (preL d (suc n)))

  rPre : ∀ {F : ℕ → P.Df W} → (∀ n → F n ≼ F n) → ∀ k → preᴰ F k ≼ preᴰ F k
  rPre r zero = L0
  rPre r (suc k) = L⨾ (rPre r k) (rPre r k) (rPre r k) (r k)

  module Steps (cl : CxLaws) where
    open CxLaws cl

    n0S : ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {x′ : D ly (tw V₂)} → Sem Aᵢ Aⱼ (n0 {W = tw V₁}) x′
    n0S {Aᵢ} {Aⱼ} {x′ = x′} q q′ w w′ c c′ Y Y′ cc g g′ s cb = ≤-trans cb (⊲→≤ (sum-fst c′ (o₀ (Run (Aⱼ) x′ q′ w′ Y′)))) , L0

    n1S : ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} → HA Aᵢ Aⱼ → Sem Aᵢ Aⱼ (n1 {W = tw V₁}) (n1 {W = tw V₂})
    n1S h q q′ w w′ c c′ Y Y′ cc g g′ s cb = h w w′ c c′ Y Y′ cc g g′ s cb

    ⨾S : ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {x y : D ly (tw V₁)} {x′ y′ : D ly (tw V₂)} → Sem Aᵢ Aᵢ x x → Sem Aⱼ Aⱼ x′ x′ → Sem Aᵢ Aⱼ x x′ → In x x′ → Sem Aᵢ Aⱼ y y′ →
         Sem Aᵢ Aⱼ (x ⨾ y) (x′ ⨾ y′)
    ⨾S {Aᵢ} {Aⱼ} {x = x} {y} {x′} {y′} rx rx′ hx ix hy q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let ox = hx q q′ w w′ c c′ Y Y′ cc g g′ s cb
          os = hx q q′ w w′ (vY Y) (vY Y′) Y Y′ cc g g′ s (proj₁ s)
          r  = rf rx q w Y (cxL cc) g
          r′ = rf rx′ q′ w′ Y′ (cxR cc) g′
          oy = hy q q′ (w ⨾ nw (emb q) x) (w′ ⨾ nw (emb q′) x′) _ _ (Y ⊕ Run (Aᵢ) x q w Y) (Y′ ⊕ Run (Aⱼ) x′ q′ w′ Y′)
                  (cx⨾ q q′ cc ix) (G⊕ g r) (G⊕ g′ r′) (S⊕ g g′ s os) (proj₁ ox)
      in proj₁ oy , L⨾ r r′ (proj₂ ox) (proj₂ oy)

    nlS : ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {d : ℕ → D ly (tw V₁)} {d′ : ℕ → D ly (tw V₂)} → (∀ n → Sem Aᵢ Aᵢ (d n) (d n)) → (∀ n → Sem Aⱼ Aⱼ (d′ n) (d′ n)) →
          (∀ n → Sem Aᵢ Aⱼ (d n) (d′ n)) → (∀ n → In (d n) (d′ n)) → Sem Aᵢ Aⱼ (nl d) (nl d′)
    nlS {Aᵢ} {Aⱼ} {d = d} {d′} rd rd′ hd id q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (proj₂ (go n)))))) , Lnl rE rE′ hE
      where
      Q  = λ n → P.Rpt ac d (emb q) lW ll (Aᵢ) w Y n
      Q′ = λ n → P.Rpt ac d′ (emb q′) lW ll (Aⱼ) w′ Y′ n
      E  = λ n → Run (Aᵢ) (d n) q (proj₁ (Q n)) (proj₂ (Q n))
      E′ = λ n → Run (Aⱼ) (d′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n))
      go : ∀ n → Cx (proj₁ (Q n)) (proj₁ (Q′ n)) × (Good (proj₂ (Q n)) × (Good (proj₂ (Q′ n)) ×
                 (SRel (proj₂ (Q n)) (proj₂ (Q′ n)) × (pt c (λ m → o₀ (E m)) n ≤ pt c′ (λ m → o₀ (E′ m)) n))))
      go zero = cc , (g , (g′ , (s , cb)))
      go (suc n) =
        let (a , (b , (b′ , (e , f)))) = go n
            h = λ e₁ e₂ (eb : e₁ ≤ e₂) → hd n q q′ (proj₁ (Q n)) (proj₁ (Q′ n)) e₁ e₂ (proj₂ (Q n)) (proj₂ (Q′ n)) a b b′ e eb
        in cx⨾ q q′ a (id n) ,
           (G⊕ {proj₂ (Q n)} b (rf (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) (cxL a) b) ,
            (G⊕ {proj₂ (Q′ n)} b′ (rf (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) (cxR a) b′) ,
             (S⊕ b b′ e (h _ _ (proj₁ e)) , proj₁ (h _ _ f))))
      rE : ∀ n → E n ≼ E n
      rE n = let (a , (b , _)) = go n in rf (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) (cxL a) b
      rE′ : ∀ n → E′ n ≼ E′ n
      rE′ n = let (a , (b , (b′ , _))) = go n in rf (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) (cxR a) b′
      hE : ∀ n → E n ≼ E′ n
      hE n = let (a , (b , (b′ , (e , f)))) = go n in
        proj₂ (hd n q q′ (proj₁ (Q n)) (proj₁ (Q′ n)) azero azero (proj₂ (Q n)) (proj₂ (Q′ n)) a b b′ e z≤)

    trS : ∀ {Aᵢ Aⱼ : Act} {V V₃} {x y : D ly (tw V)} {z : D ly (tw V₃)} → Sem Aᵢ Aᵢ x y → Sem Aᵢ Aⱼ y z → Sem Aᵢ Aⱼ x z
    trS h h′ q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let o = h q q w w c c Y Y (cxL cc) g g (sr g) (≤-refl c)
          o′ = h′ q q′ w w′ c c′ Y Y′ cc g g′ s cb
      in ≤-trans (proj₁ o) (proj₁ o′) , Ltr (proj₂ o) (proj₂ o′)

    trS′ : ∀ {Aᵢ Aⱼ : Act} {V V₁} {x : D ly (tw V₁)} {y z : D ly (tw V)} → Sem Aᵢ Aⱼ x y → Sem Aⱼ Aⱼ y z → Sem Aᵢ Aⱼ x z
    trS′ h h′ q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let o = h q q′ w w′ c c′ Y Y′ cc g g′ s cb
          o′ = h′ q′ q′ w′ w′ c′ c′ Y′ Y′ (cxR cc) g′ g′ (sr g′) (≤-refl c′)
      in ≤-trans (proj₁ o) (proj₁ o′) , Ltr (proj₂ o) (proj₂ o′)

    u0ˡS : ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {x : D ly (tw V₁)} {x′ : D ly (tw V₂)} → Sem Aᵢ Aⱼ x x′ → Sem Aᵢ Aⱼ (n0 ⨾ x) x′
    u0ˡS h q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let o = h q q′ (w ⨾ nw (emb q) n0) w′ c c′ (Y ⊕ P.zeroD) Y′ (cx0ˡ q cc) (L⨾ g g g L0) g′ (proj₁ s , Lu1ˡ (proj₂ s)) cb
      in proj₁ o , Lu0ˡ (proj₂ o)

    u0ʳS : ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {x : D ly (tw V₁)} {x′ : D ly (tw V₂)} → Sem Aᵢ Aⱼ x x′ → Sem Aᵢ Aⱼ x (n0 ⨾ x′)
    u0ʳS h q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let o = h q q′ w (w′ ⨾ nw (emb q′) n0) c c′ Y (Y′ ⊕ P.zeroD) (cx0ʳ q′ cc) g (L⨾ g′ g′ g′ L0) (proj₁ s , Lu1ʳ (proj₂ s)) cb
      in proj₁ o , Lu0ʳ (proj₂ o)

    u1ˡS : ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {x : D ly (tw V₁)} {x′ : D ly (tw V₂)} → Sem Aᵢ Aⱼ x x′ → Sem Aᵢ Aⱼ (x ⨾ n0) x′
    u1ˡS h q q′ w w′ c c′ Y Y′ cc g g′ s cb = let o = h q q′ w w′ c c′ Y Y′ cc g g′ s cb in proj₁ o , Lu1ˡ (proj₂ o)

    u1ʳS : ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {x : D ly (tw V₁)} {x′ : D ly (tw V₂)} → Sem Aᵢ Aⱼ x x′ → Sem Aᵢ Aⱼ x (x′ ⨾ n0)
    u1ʳS h q q′ w w′ c c′ Y Y′ cc g g′ s cb = let o = h q q′ w w′ c c′ Y Y′ cc g g′ s cb in proj₁ o , Lu1ʳ (proj₂ o)

    -- 一边走三段 x, y, z
    module Three (a : Act) {V} (x y z : D ly (tw V)) (sx : Sem a a x x) (sy : Sem a a y y) (ix : In x x) (iy : In y y)
                 (q : Path V) (w : D ly W) (cw : Cx w w) (Y : P.St W) (g : Good Y) where
      Rx = Run (a) x q w Y
      rX = rf sx q w Y cw g
      gx = G⊕ {Y} {Rx} g rX
      Ry = Run (a) y q (w ⨾ nw (emb q) x) (Y ⊕ Rx)
      rY = rf sy q (w ⨾ nw (emb q) x) (Y ⊕ Rx) (cx⨾ q q cw ix) gx
      S1 = Y ⊕ (Rx P.⨾ᴰ Ry)
      S2 = (Y ⊕ Rx) ⊕ Ry
      rXY = L⨾ rX rX rX rY
      gS1 : Good S1
      gS1 = L⨾ g g g rXY
      gS2 : Good S2
      gS2 = G⊕ {Y ⊕ Rx} {Ry} gx rY
      s12 : SRel S1 S2
      s12 = ≤-refl _ , Lasʳ′ g rX rY gS1
      s21 : SRel S2 S1
      s21 = ≤-refl _ , Lasˡ g rX rY gS1
      w1 = w ⨾ nw (emb q) (x ⨾ y)
      w2 = (w ⨾ nw (emb q) x) ⨾ nw (emb q) y
      c12 = cxas q cw ix iy
      c21 = cxas′ q cw ix iy

    asˡS : ∀ {Aᵢ Aⱼ : Act} {V V′} {x y z : D ly (tw V)} {t : D ly (tw V′)} → Sem Aᵢ Aᵢ x x → Sem Aᵢ Aᵢ y y → Sem Aᵢ Aᵢ z z → In x x → In y y →
           Sem Aᵢ Aⱼ (x ⨾ (y ⨾ z)) t → Sem Aᵢ Aⱼ ((x ⨾ y) ⨾ z) t
    asˡS {Aᵢ} {x = x} {y} {z} sx sy sz ix iy h q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let open Three Aᵢ x y z sx sy ix iy q w (cxL cc) Y g
          b = sum (sum c (o₀ Rx)) (o₀ Ry)
          oz = sz q q w1 w2 b b S1 S2 c12 gS1 gS2 s12 (≤-refl b)
          rZ = rf sz q w1 S1 (cxL c12) gS1
          oh = h q q′ w w′ c c′ Y Y′ cc g g′ s cb
      in ≤-trans (proj₁ oz) (proj₁ oh) , Lasˡ rX rY rZ (Ltr (L⨾ rX rX rX (L⨾ rY rY rY (proj₂ oz))) (proj₂ oh))

    asˡ′S : ∀ {Aᵢ Aⱼ : Act} {V V′} {x y z : D ly (tw V)} {t : D ly (tw V′)} → Sem Aᵢ Aᵢ x x → Sem Aᵢ Aᵢ y y → Sem Aᵢ Aᵢ z z → In x x → In y y →
            Sem Aᵢ Aⱼ ((x ⨾ y) ⨾ z) t → Sem Aᵢ Aⱼ (x ⨾ (y ⨾ z)) t
    asˡ′S {Aᵢ} {x = x} {y} {z} sx sy sz ix iy h q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let open Three Aᵢ x y z sx sy ix iy q w (cxL cc) Y g
          b = sum (sum c (o₀ Rx)) (o₀ Ry)
          oz = sz q q w2 w1 b b S2 S1 c21 gS2 gS1 s21 (≤-refl b)
          rZ = rf sz q w2 S2 (cxL c21) gS2
          oh = h q q′ w w′ c c′ Y Y′ cc g g′ s cb
      in ≤-trans (proj₁ oz) (proj₁ oh) , Lasˡ′ rX rY rZ (Ltr (L⨾ rXY rXY rXY (proj₂ oz)) (proj₂ oh))

    asʳS : ∀ {Aᵢ Aⱼ : Act} {V V′} {x y z : D ly (tw V)} {t : D ly (tw V′)} → Sem Aⱼ Aⱼ x x → Sem Aⱼ Aⱼ y y → Sem Aⱼ Aⱼ z z → In x x → In y y →
           Sem Aᵢ Aⱼ t ((x ⨾ y) ⨾ z) → Sem Aᵢ Aⱼ t (x ⨾ (y ⨾ z))
    asʳS {Aᵢ} {Aⱼ} {x = x} {y} {z} sx sy sz ix iy h q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let open Three Aⱼ x y z sx sy ix iy q′ w′ (cxR cc) Y′ g′
          b = sum (sum c′ (o₀ Rx)) (o₀ Ry)
          oz = sz q′ q′ w1 w2 b b S1 S2 c12 gS1 gS2 s12 (≤-refl b)
          rZ = rf sz q′ w2 S2 (cxR c12) gS2
          oh = h q q′ w w′ c c′ Y Y′ cc g g′ s cb
      in ≤-trans (proj₁ oh) (proj₁ oz) , Lasʳ rX rY rZ (Ltr (proj₂ oh) (L⨾ rXY rXY rXY (proj₂ oz)))

    asʳ′S : ∀ {Aᵢ Aⱼ : Act} {V V′} {x y z : D ly (tw V)} {t : D ly (tw V′)} → Sem Aⱼ Aⱼ x x → Sem Aⱼ Aⱼ y y → Sem Aⱼ Aⱼ z z → In x x → In y y →
            Sem Aᵢ Aⱼ t (x ⨾ (y ⨾ z)) → Sem Aᵢ Aⱼ t ((x ⨾ y) ⨾ z)
    asʳ′S {Aᵢ} {Aⱼ} {x = x} {y} {z} sx sy sz ix iy h q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      let open Three Aⱼ x y z sx sy ix iy q′ w′ (cxR cc) Y′ g′
          b = sum (sum c′ (o₀ Rx)) (o₀ Ry)
          oz = sz q′ q′ w2 w1 b b S2 S1 c21 gS2 gS1 s21 (≤-refl b)
          rZ = rf sz q′ w1 S1 (cxR c21) gS1
          oh = h q q′ w w′ c c′ Y Y′ cc g g′ s cb
      in ≤-trans (proj₁ oh) (proj₁ oz) , Lasʳ′ rX rY rZ (Ltr (proj₂ oh) (L⨾ rX rX rX (L⨾ rY rY rY (proj₂ oz))))
```
```agda
    preS : PreLaw O → ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {x : D ly (tw V₁)} {x′ : D ly (tw V₂)} {d : ℕ → D ly (tw V₁)} {d′ : ℕ → D ly (tw V₂)} →
           Sem Aᵢ Aᵢ x x → Sem Aⱼ Aⱼ x′ x′ → (∀ n → Sem Aᵢ Aᵢ (d n) (d n)) → (∀ n → Sem Aⱼ Aⱼ (d′ n) (d′ n)) →
           Sem Aᵢ Aⱼ x x′ → In x x′ → (∀ n → Sem Aᵢ Aⱼ (d n) (d′ n)) → (∀ n → In (d n) (d′ n)) → ∀ k → Sem Aᵢ Aⱼ (x ⨾ preL d k) (x′ ⨾ nl d′)
    preS Lpre {Aᵢ} {Aⱼ} {x = x} {x′} {d} {d′} rx rx′ rd rd′ hx ix hd id k q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      ≤l k (proj₂ (proj₂ (proj₂ (proj₂ (go k))))) ,
      subst (λ t → (Rx P.⨾ᴰ t) ≼ (Rx′ P.⨾ᴰ P.nlᴰ E′)) (sym (L.O≡ k)) (Lpre rX rX′ rE rE′ (proj₂ ox) hE k)
      where
      Rx = Run (Aᵢ) x q w Y
      Rx′ = Run (Aⱼ) x′ q′ w′ Y′
      ox = hx q q′ w w′ c c′ Y Y′ cc g g′ s cb
      rX = rf rx q w Y (cxL cc) g
      rX′ = rf rx′ q′ w′ Y′ (cxR cc) g′
      Z = Y ⊕ Rx
      Z′ = Y′ ⊕ Rx′
      w₁ = w ⨾ nw (emb q) x
      w₁′ = w′ ⨾ nw (emb q′) x′
      gZ : Good Z
      gZ = G⊕ {Y} {Rx} g rX
      gZ′ : Good Z′
      gZ′ = G⊕ {Y′} {Rx′} g′ rX′
      sZ : SRel Z Z′
      sZ = S⊕ g g′ s (hx q q′ w w′ (vY Y) (vY Y′) Y Y′ cc g g′ s (proj₁ s))
      module L = PreOut (Aᵢ) d q w₁ Z
      Q′ = λ n → P.Rpt ac d′ (emb q′) lW ll (Aⱼ) w₁′ Z′ n
      E′ = λ n → Run (Aⱼ) (d′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n))
      b₁ = sum c (o₀ Rx)
      b₁′ = sum c′ (o₀ Rx′)
      go : ∀ n → (L.Rp n ≼ L.Rp n) × (Cx (w₁ ⨾ nw (emb q) (preL d n)) (proj₁ (Q′ n)) × (Good (proj₂ (Q′ n)) ×
                 (SRel (Z ⊕ L.Rp n) (proj₂ (Q′ n)) × (sum b₁ (o₀ (L.Rp n)) ≤ pt b₁′ (λ m → o₀ (E′ m)) n))))
      go zero = L0 , (cx0ˡ q (cx⨾ q q′ cc ix) , (gZ′ , ((proj₁ sZ , Lu1ˡ (proj₂ sZ)) , proj₁ ox)))
      go (suc n) =
        let (a , (cn , (gr , (e , f)))) = go n
            gLn = G⊕ {Z} {L.Rp n} gZ a
            h = λ e₁ e₂ (eb : e₁ ≤ e₂) → hd n q q′ (w₁ ⨾ nw (emb q) (preL d n)) (proj₁ (Q′ n)) e₁ e₂ (Z ⊕ L.Rp n) (proj₂ (Q′ n)) cn gLn gr e eb
            rEn = rf (rd n) q (w₁ ⨾ nw (emb q) (preL d n)) (Z ⊕ L.Rp n) (cxL cn) gLn
        in L⨾ a a a rEn ,
           (cxpre q q′ n cn (id n) ,
            (G⊕ {proj₂ (Q′ n)} gr (rf (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) (cxR cn) gr) ,
             ((proj₁ (h _ _ (proj₁ e)) , Lasˡ′ gZ a rEn (L⨾ gLn gr (proj₂ e) (proj₂ (h azero azero z≤)))) ,
              proj₁ (h _ _ f))))
      rE : ∀ n → L.Ek n ≼ L.Ek n
      rE n = let (a , (cn , _)) = go n in rf (rd n) q (w₁ ⨾ nw (emb q) (preL d n)) (Z ⊕ L.Rp n) (cxL cn) (G⊕ {Z} {L.Rp n} gZ a)
      rE′ : ∀ n → E′ n ≼ E′ n
      rE′ n = let (a , (cn , (gr , _))) = go n in rf (rd′ n) q′ (proj₁ (Q′ n)) (proj₂ (Q′ n)) (cxR cn) gr
      hE : ∀ n → L.Ek n ≼ E′ n
      hE n = let (a , (cn , (gr , (e , f)))) = go n in
        proj₂ (hd n q q′ (w₁ ⨾ nw (emb q) (preL d n)) (proj₁ (Q′ n)) azero azero (Z ⊕ L.Rp n) (proj₂ (Q′ n)) cn (G⊕ {Z} {L.Rp n} gZ a) gr e z≤)

    limS : LimLaw O → ∀ {Aᵢ Aⱼ : Act} {V₁ V₂} {x : D ly (tw V₁)} {d : ℕ → D ly (tw V₁)} {t : D ly (tw V₂)} →
           Sem Aᵢ Aᵢ x x → (∀ n → Sem Aᵢ Aᵢ (d n) (d n)) → In x x → (∀ n → In (d n) (d n)) →
           (∀ k → Sem Aᵢ Aⱼ (x ⨾ preL d k) t) → Sem Aᵢ Aⱼ (x ⨾ nl d) t
    limS Llim {Aᵢ} {Aⱼ} {x = x} {d} {t} rx rd ix id hk q q′ w w′ c c′ Y Y′ cc g g′ s cb =
      l≤ (λ k → ≤-trans (proj₂ (proj₂ (proj₂ (proj₂ (go k))))) (proj₁ (hk k q q′ w w′ c c′ Y Y′ cc g g′ s cb))) ,
      Llim rX rEL (λ k → Ltr (L⨾ rX rX rX (PL k))
                             (subst (λ t′ → (Rx P.⨾ᴰ t′) ≼ Run (Aⱼ) t q′ w′ Y′) (L.O≡ k) (proj₂ (hk k q q′ w w′ c c′ Y Y′ cc g g′ s cb))))
      where
      Rx = Run (Aᵢ) x q w Y
      cw = cxL cc
      rX = rf rx q w Y cw g
      Z = Y ⊕ Rx
      w₁ = w ⨾ nw (emb q) x
      gZ : Good Z
      gZ = G⊕ {Y} {Rx} g rX
      module L = PreOut (Aᵢ) d q w₁ Z
      Q = λ n → P.Rpt ac d (emb q) lW ll (Aᵢ) w₁ Z n
      EL = λ n → Run (Aᵢ) (d n) q (proj₁ (Q n)) (proj₂ (Q n))
      b₁ = sum c (o₀ Rx)
      go : ∀ n → (L.Rp n ≼ L.Rp n) × (Cx (proj₁ (Q n)) (w₁ ⨾ nw (emb q) (preL d n)) × (Good (proj₂ (Q n)) ×
                 (SRel (proj₂ (Q n)) (Z ⊕ L.Rp n) × (pt b₁ (λ m → o₀ (EL m)) n ≤ sum b₁ (o₀ (L.Rp n))))))
      go zero = L0 , (cx0ʳ q (cx⨾ q q cw ix) , (gZ , ((≤-refl _ , Lu1ʳ gZ) , ≤-refl _)))
      go (suc n) =
        let (a , (cn , (gq , (e , f)))) = go n
            gLn = G⊕ {Z} {L.Rp n} gZ a
            h = λ e₁ e₂ (eb : e₁ ≤ e₂) → rd n q q (proj₁ (Q n)) (w₁ ⨾ nw (emb q) (preL d n)) e₁ e₂ (proj₂ (Q n)) (Z ⊕ L.Rp n) cn gq gLn e eb
            rEk = rf (rd n) q (w₁ ⨾ nw (emb q) (preL d n)) (Z ⊕ L.Rp n) (cxR cn) gLn
        in L⨾ a a a rEk ,
           (cxlim q n cn (id n) ,
            (G⊕ {proj₂ (Q n)} gq (rf (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) (cxL cn) gq) ,
             ((proj₁ (h _ _ (proj₁ e)) , Lasʳ gZ a rEk (L⨾ gq gLn (proj₂ e) (proj₂ (h azero azero z≤)))) ,
              proj₁ (h _ _ f))))
      rEL : ∀ n → EL n ≼ EL n
      rEL n = let (a , (cn , (gq , _))) = go n in rf (rd n) q (proj₁ (Q n)) (proj₂ (Q n)) (cxL cn) gq
      rEk : ∀ n → L.Ek n ≼ L.Ek n
      rEk n = let (a , (cn , _)) = go n in rf (rd n) q (w₁ ⨾ nw (emb q) (preL d n)) (Z ⊕ L.Rp n) (cxR cn) (G⊕ {Z} {L.Rp n} gZ a)
      hEL : ∀ n → EL n ≼ L.Ek n
      hEL n = let (a , (cn , (gq , (e , f)))) = go n in
        proj₂ (rd n q q (proj₁ (Q n)) (w₁ ⨾ nw (emb q) (preL d n)) azero azero (proj₂ (Q n)) (Z ⊕ L.Rp n) cn gq (G⊕ {Z} {L.Rp n} gZ a) e z≤)
      PL : ∀ k → preᴰ EL k ≼ preᴰ L.Ek k
      PL zero = L0
      PL (suc k) = L⨾ (rPre rEL k) (rPre rEk k) (PL k) (hEL k)
```
