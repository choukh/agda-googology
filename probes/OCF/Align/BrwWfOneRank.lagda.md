# 沿 View 递归 (六): 第 1 层布劳威尔树的秩, 抬升不升秩

> 不含记号. 入口 [BrwWf](BrwWf.lagda.md). 第 1 层 View 的 $\Omega$-极限的部分是 "前缀抬到大世界再求值, 接一段积分", 值与整体的分支只是 $\approx$ (要 `HW`), 不是字面相等. 这里换一个度量: 值 `toB` 在**秩的比较** $\sqsubseteq$ ([BrwWfRank](BrwWfRank.lagda.md)) 下比. 直接子树 `Sub₁` 取 `B₁` 的五种构造子, `bw` 透明.
>
> 核心是 `Rv` (**抬升不升秩, 无条件**): 差树 $y$ 在更大的世界 $W'$ 里求值, 秩不超过在 $W$ 里求值:
>
> $$b'\sqsubseteq b\ \Rightarrow\ S_{q\cdot p}(b',y)\sqsubseteq S_q(b,y).$$
>
> 原因: 在大世界里, `ni` 的分支只取更大世界上的, `nκ` 的分支只取更高的层, 各是小世界里分支的**一部分** (坐标映射 $p''\mapsto p\cdot p''$), 层上的段 `K` 从 $W'$ 起走, 是从 $W$ 起走的那一段的后缀 (`Ksuf`). 秩的比较只要 "左边每个直接子树低于右边某个直接子树", 所以 "一部分" 就够了. 值的比较 $\approx$ 要两个方向, 反方向就是 `WSq`, 它不是无条件的 ([BrwViewLift](BrwViewLift.lagda.md) `lift-fails`). **秩只要一个方向, 这个方向无条件.**
>
> 其余: 构造子单调 (`bs-⊑`, `bl-⊑`, `bi-⊑`, `bκ-⊑`, 坐标可以重排), `bw` 两边透明, 第一位置低于整体 (`⊲→⊑`), `S`, `I`, `K` 对底单调 (`Smono`, `Imono`, `Kmono`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWfOneRank where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; Pre; tailP)
open import OCF.Align.BrwMidZero using (dif)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp; I; Ip; K; KR; toB; K-fst; ok-yes)
open import OCF.Align.BrwViewOne using (⊲-assoc)
open import OCF.Align.BrwWfRank
```

## §1 直接子树

```agda
T₁ : Set
T₁ = Σ A B₁

data Sub₁ : T₁ → T₁ → Set where
  s-s : ∀ {W} {a : B₁ W} → Sub₁ (W , a) (W , bs a)
  s-l : ∀ {W} {f : ℕ → B₁ W} n → Sub₁ (W , f n) (W , bl f)
  s-i : ∀ {W} {f : ∀ {W′} → W ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′} {W′} (p : W ⊲ W′) (l : Lg W′) y ly →
        Sub₁ (W′ , f p l y ly) (W , bi f)
  s-κ : ∀ {W} {g : ∀ {c} → W ⊲ c → Lg c → B₁ c} {c} (p : W ⊲ c) (l : Lg c) → Sub₁ (c , g p l) (W , bκ g)
  s-w : ∀ {W₀ W} {p : W₀ ⊲ W} {b : B₁ W₀} {t} → Sub₁ t (W₀ , b) → Sub₁ t (W , bw p b)

inv : ∀ {t u} → Acc Sub₁ u → Sub₁ t u → Acc Sub₁ t
inv (acc rs) r = rs r

Sub₁-acc : ∀ W (b : B₁ W) → Acc Sub₁ (W , b)
Sub₁-acc W bz = acc (λ ())
Sub₁-acc W (bs a) = acc (λ { s-s → Sub₁-acc W a })
Sub₁-acc W (bl f) = acc (λ { (s-l n) → Sub₁-acc W (f n) })
Sub₁-acc W (bi f) = acc (λ { (s-i p l y ly) → Sub₁-acc _ (f p l y ly) })
Sub₁-acc W (bκ g) = acc (λ { (s-κ p l) → Sub₁-acc _ (g p l) })
Sub₁-acc W (bw p b) = acc (λ { (s-w r) → inv (Sub₁-acc _ b) r })

Sub₁-wf : WellFounded Sub₁
Sub₁-wf (W , b) = Sub₁-acc W b

open Rank Sub₁ Sub₁-wf public

infix 4 _⊑_
_⊑_ : ∀ {W W′} → B₁ W → B₁ W′ → Set
a ⊑ b = (_ , a) ≤ₛ (_ , b)

⊑-refl : ∀ {W} (a : B₁ W) → a ⊑ a
⊑-refl a = ≤ₛ-refl (_ , a)

⊑-trans : ∀ {W₁ W₂ W₃} {a : B₁ W₁} {b : B₁ W₂} {c : B₁ W₃} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans = ≤ₛ-trans
```

## §2 构造子单调, `bw` 透明, 第一位置

```agda
z⊑ : ∀ {W W′} {b : B₁ W′} → bz {W} ⊑ b
z⊑ = sim (λ ())

bs-⊑ : ∀ {W W′} {a : B₁ W} {b : B₁ W′} → a ⊑ b → bs a ⊑ bs b
bs-⊑ h = sim (λ { s-s → lt s-s h })

bl-⊑ : ∀ {W W′} {f : ℕ → B₁ W} {g : ℕ → B₁ W′} → (∀ n → f n ⊑ g n) → bl f ⊑ bl g
bl-⊑ h = sim (λ { (s-l n) → lt (s-l n) (h n) })

-- 坐标可以重排: 左边的分支 (世界 W 之上) 映到右边的分支 (世界 V 之上)
bi-⊑ : ∀ {W V} {f : ∀ {W′} → W ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′} {g : ∀ {W′} → V ⊲ W′ → Lg W′ → (y : A) → Lg y → B₁ W′}
       (m : ∀ {W′} → W ⊲ W′ → V ⊲ W′) → (∀ {W′} p l y ly → f {W′} p l y ly ⊑ g (m p) l y ly) → bi f ⊑ bi g
bi-⊑ m h = sim (λ { (s-i p l y ly) → lt (s-i (m p) l y ly) (h p l y ly) })

bκ-⊑ : ∀ {W V} {f : ∀ {c} → W ⊲ c → Lg c → B₁ c} {g : ∀ {c} → V ⊲ c → Lg c → B₁ c}
       (m : ∀ {c} → W ⊲ c → V ⊲ c) → (∀ {c} p l → f {c} p l ⊑ g (m p) l) → bκ f ⊑ bκ g
bκ-⊑ m h = sim (λ { (s-κ p l) → lt (s-κ (m p) l) (h p l) })

w⊑ : ∀ {W₀ W W′} {p : W₀ ⊲ W} {a : B₁ W₀} {b : B₁ W′} → a ⊑ b → bw p a ⊑ b
w⊑ (sim h) = sim (λ { (s-w r) → h r })

⊑w : ∀ {W₀ W W′} {p : W₀ ⊲ W} {a : B₁ W′} {b : B₁ W₀} → a ⊑ b → a ⊑ bw p b
⊑w {p = p} {b = b} (sim h) = sim (λ r → wr (h r))
  where
  wr : ∀ {t} → t <ₛ (_ , b) → t <ₛ (_ , bw p b)
  wr (lt rb le) = lt (s-w rb) le

⊲→⊑ : ∀ {W W′ fl} {a : B₁ W} {b : B₁ W′} → a ⊲⟨ fl ⟩ b → a ⊑ b
⊲→⊑ self = ⊑-refl _
⊲→⊑ (suc P) = ⊑-trans (⊲→⊑ P) (sub≤ s-s)
⊲→⊑ (lim n P) = ⊑-trans (⊲→⊑ P) (sub≤ (s-l n))
⊲→⊑ (wR P) = ⊑w (⊲→⊑ P)
⊲→⊑ (wL P) = w⊑ (⊲→⊑ P)
⊲→⊑ (ini l P) = ⊑-trans (⊲→⊑ P) (sub≤ (s-i C.self l azero tt))
⊲→⊑ (inκ l P) = ⊑-trans (⊲→⊑ P) (sub≤ (s-κ C.self l))
```

## §3 对底单调

```agda
Imono  : ∀ {W₀ W} (e : D azero W → B₁ W → B₁ W) → (∀ w {b b′} → b ⊑ b′ → e w b ⊑ e w b′) →
         (z : D azero W₀) (q : W₀ ⊲ W) → ∀ w {b b′} → b ⊑ b′ → I e z q w b ⊑ I e z q w b′
Ipmono : ∀ {W₀ W} (e : D azero W → B₁ W → B₁ W) → (∀ w {b b′} → b ⊑ b′ → e w b ⊑ e w b′) →
         (d : ℕ → D azero W₀) (q : W₀ ⊲ W) → ∀ w {b b′} → b ⊑ b′ → ∀ n → Ip e d q w b n ⊑ Ip e d q w b′ n
Imono e m n0 q w h = h
Imono e m n1 q w h = m w h
Imono e m (x ⨾ y) q w h = Imono e m y q (w ⨾ nw q x) (Imono e m x q w h)
Imono e m (nl d) q w h = bl-⊑ (Ipmono e m d q w h)
Imono e m (ni () u) q w h
Imono e m (nκ () u) q w h
Imono e m (nw p x) q w h = Imono e m x (⊲-tr p q) w h
Ipmono e m d q w h zero = h
Ipmono e m d q w h (suc n) = Imono e m (d n) q (w ⨾ Pre q d n) (Ipmono e m d q w h n)

-- 段的单调作参数 (分支的 S 单调), 不对 K 的分支递归
module _ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c)
         (mu : ∀ {c} (r : W₀ ⊲ c) (lr : Lg c) {x x′ : B₁ c} → x ⊑ x′ → S C.self lr x (u r lr) ⊑ S C.self lr x′ (u r lr)) where
  Kmono  : ∀ b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) {x x′ : B₁ a} → x ⊑ x′ → K u b p aW lb x ⊑ K u b p aW lb x′
  KRmono : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (aW : W₀ ⊲ a)
           {x x′ : B₁ a} → x ⊑ x′ → ∀ m → KR u f st wl p aW x m ⊑ KR u f st wl p aW x′ m
  Kmono b C.self aW lb h = h
  Kmono (asuc c) (C.suc p) aW lb h = w⊑ (⊑w (mu (⊲-tr aW p) lb (Kmono c p aW lb h)))
  Kmono (alim f) (C.lim n p) aW (st , wl) h = bl-⊑ (λ m → w⊑ (⊑w (KRmono f st wl p aW h m)))
  KRmono f st wl p aW h zero = Kmono (f _) p aW (wl _) h
  KRmono f st wl {n = n} p aW h (suc m) =
    Kmono (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (KRmono f st wl p aW h m)

Smono  : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (y : D one W₀) {b b′ : B₁ W} → b ⊑ b′ → S q l b y ⊑ S q l b′ y
Smonop : ∀ {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (d : ℕ → D one W₀) {b b′ : B₁ W} → b ⊑ b′ → ∀ n → Sp q l b d n ⊑ Sp q l b′ d n
Smono q l n0 h = h
Smono q l n1 h = bs-⊑ h
Smono q l (x ⨾ y) h = Smono q l y (Smono q l x h)
Smono q l (nl d) h = bl-⊑ (Smonop q l d h)
Smono q l (ni (ss C.self) u) h =
  bi-⊑ (λ p → p) (λ p l′ y ly → Imono _ (λ w h′ → Smono C.self l′ (u (⊲-tr q p) l′ w) h′) (dif y (z⊲ y) ly) C.self n0 (w⊑ (⊑w h)))
Smono q l (nκ zz u) h =
  bκ-⊑ (λ p → p) (λ p lc → Smono C.self lc (u (⊲-tr q p) lc) (Kmono u (λ r lr h′ → Smono C.self lr (u r lr) h′) _ p q lc h))
Smono q l (nw p x) h = Smono (⊲-tr p q) l x h
Smonop q l d h zero = h
Smonop q l d h (suc n) = Smono q l (d n) (Smonop q l d h n)

mS : ∀ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) {c} (r : W₀ ⊲ c) (lr : Lg c) {x x′ : B₁ c} → x ⊑ x′ →
     S C.self lr x (u r lr) ⊑ S C.self lr x′ (u r lr)
mS u r lr h = Smono C.self lr (u r lr) h
```

## §4 层上的段: 后缀不升秩

`Ksuf`: 从 $W'$ 起沿 $p''$ 走到 $c$ 的段 (底 $b'$), 秩不超过从 $W$ 起沿 $p\cdot p''$ 走到 $c$ 的段 (底 $b$). 对路径 $p''$ 归纳; 起点处 ($p''$ = `self`) 用 "底低于底加一段" (`K-fst` 与 `⊲→⊑`). 路径的结合用 `⊲-assoc` 与 `tailP-tr` 搬运.

```agda
tailP-tr : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) {a b n} (p : a ⊲ b) (p₀ : b ⊲ f n) m →
           tailP f st (⊲-tr p p₀) m ≡ ⊲-tr p (tailP f st p₀ m)
tailP-tr f st p p₀ zero = refl
tailP-tr f st {n = n} p p₀ (suc m) =
  trans (cong (λ t → ⊲-tr t (st (m + n))) (tailP-tr f st p p₀ m)) (⊲-assoc p (tailP f st p₀ m) (st (m + n)))

module _ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) where
  Ksuf  : ∀ {W W′} c (p″ : W′ ⊲ c) (q : W₀ ⊲ W) (p : W ⊲ W′) (lc : Lg c) {b : B₁ W} {b′ : B₁ W′} → b′ ⊑ b →
          K u c p″ (⊲-tr q p) lc b′ ⊑ K u c (⊲-tr p p″) q lc b
  KRsuf : ∀ {W W′} (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {n} (p₀ : W′ ⊲ f n)
          (q : W₀ ⊲ W) (p : W ⊲ W′) {b : B₁ W} {b′ : B₁ W′} → b′ ⊑ b →
          ∀ m → KR u f st wl p₀ (⊲-tr q p) b′ m ⊑ KR u f st wl (⊲-tr p p₀) q b m
  Ksuf c C.self q p lc {b} h = ⊑-trans h (⊲→⊑ (K-fst yes u (λ r l → ok-yes (u r l)) c p q lc b))
  Ksuf (asuc c) (C.suc p₀) q p lc {b} {b′} h =
    w⊑ (⊑w (subst (λ t → S C.self lc (K u c p₀ (⊲-tr q p) lc b′) (u t lc) ⊑ S C.self lc (K u c (⊲-tr p p₀) q lc b) (u (⊲-tr q (⊲-tr p p₀)) lc))
                  (sym (⊲-assoc q p p₀))
                  (mS u (⊲-tr q (⊲-tr p p₀)) lc (Ksuf c p₀ q p lc h))))
  Ksuf (alim f) (C.lim n p₀) q p (st , wl) h = bl-⊑ (λ m → w⊑ (⊑w (KRsuf f st wl p₀ q p h m)))
  KRsuf f st wl p₀ q p h zero = Ksuf (f _) p₀ q p (wl _) h
  KRsuf f st wl {n} p₀ q p {b} {b′} h (suc m) =
    subst (λ t → K u (f (suc (m + n))) (st (m + n)) t (wl (suc (m + n))) (KR u f st wl p₀ (⊲-tr q p) b′ m) ⊑
                 K u (f (suc (m + n))) (st (m + n)) (⊲-tr q (tailP f st (⊲-tr p p₀) m)) (wl (suc (m + n))) (KR u f st wl (⊲-tr p p₀) q b m))
          (sym E)
          (Kmono u (mS u) (f (suc (m + n))) (st (m + n)) _ (wl (suc (m + n))) (KRsuf f st wl p₀ q p h m))
    where
    E : ⊲-tr (⊲-tr q p) (tailP f st p₀ m) ≡ ⊲-tr q (tailP f st (⊲-tr p p₀) m)
    E = trans (⊲-assoc q p (tailP f st p₀ m)) (cong (⊲-tr q) (sym (tailP-tr f st p p₀ m)))
```

## §5 抬升不升秩

```agda
Rv  : ∀ {W₀ W W′} (y : D one W₀) (q : W₀ ⊲ W) (p : W ⊲ W′) (l : Lg W) (l′ : Lg W′) {b : B₁ W} {b′ : B₁ W′} →
      b′ ⊑ b → S (⊲-tr q p) l′ b′ y ⊑ S q l b y
Rvp : ∀ {W₀ W W′} (d : ℕ → D one W₀) (q : W₀ ⊲ W) (p : W ⊲ W′) (l : Lg W) (l′ : Lg W′) {b : B₁ W} {b′ : B₁ W′} →
      b′ ⊑ b → ∀ n → Sp (⊲-tr q p) l′ b′ d n ⊑ Sp q l b d n
Rv n0 q p l l′ h = h
Rv n1 q p l l′ h = bs-⊑ h
Rv (x ⨾ y) q p l l′ h = Rv y q p l l′ (Rv x q p l l′ h)
Rv (nl d) q p l l′ h = bl-⊑ (Rvp d q p l l′ h)
Rv (ni (ss C.self) u) q p l l′ {b} {b′} h = bi-⊑ (⊲-tr p) br
  where
  br : ∀ {W″} (p″ : _ ⊲ W″) (l″ : Lg W″) y ly →
       I (λ w b″ → S C.self l″ b″ (u (⊲-tr (⊲-tr q p) p″) l″ w)) (dif y (z⊲ y) ly) C.self n0 (bw p″ b′) ⊑
       I (λ w b″ → S C.self l″ b″ (u (⊲-tr q (⊲-tr p p″)) l″ w)) (dif y (z⊲ y) ly) C.self n0 (bw (⊲-tr p p″) b)
  br p″ l″ y ly =
    subst (λ t → I (λ w b″ → S C.self l″ b″ (u t l″ w)) (dif y (z⊲ y) ly) C.self n0 (bw p″ b′) ⊑
                 I (λ w b″ → S C.self l″ b″ (u (⊲-tr q (⊲-tr p p″)) l″ w)) (dif y (z⊲ y) ly) C.self n0 (bw (⊲-tr p p″) b))
          (sym (⊲-assoc q p p″))
          (Imono _ (λ w h′ → Smono C.self l″ (u (⊲-tr q (⊲-tr p p″)) l″ w) h′) (dif y (z⊲ y) ly) C.self n0 (w⊑ (⊑w h)))
Rv (nκ zz u) q p l l′ {b} {b′} h = bκ-⊑ (⊲-tr p) br
  where
  br : ∀ {c} (p″ : _ ⊲ c) (lc : Lg c) →
       S C.self lc (K u c p″ (⊲-tr q p) lc b′) (u (⊲-tr (⊲-tr q p) p″) lc) ⊑
       S C.self lc (K u c (⊲-tr p p″) q lc b) (u (⊲-tr q (⊲-tr p p″)) lc)
  br {c} p″ lc =
    subst (λ t → S C.self lc (K u c p″ (⊲-tr q p) lc b′) (u t lc) ⊑ S C.self lc (K u c (⊲-tr p p″) q lc b) (u (⊲-tr q (⊲-tr p p″)) lc))
          (sym (⊲-assoc q p p″))
          (mS u (⊲-tr q (⊲-tr p p″)) lc (Ksuf u c p″ q p lc h))
Rv (nw r y) q p l l′ {b} {b′} h =
  subst (λ t → S t l′ b′ y ⊑ S (⊲-tr r q) l b y) (⊲-assoc r q p) (Rv y (⊲-tr r q) p l l′ h)
Rvp d q p l l′ h zero = h
Rvp d q p l l′ h (suc n) = Rv (d n) q p l l′ (Rvp d q p l l′ h n)
```

**读法.** `Rv` 没有前提: 一切第 1 层差树, 抬到更大的世界再求值, 秩不升. 对比 `BrwViewOne.lift` (值不变) 要 `HW`, 而且 `BrwViewLift.lift-fails` 给出不满足的树: 那棵树抬升后值从 $\ge1$ 降到 $0$, 降是允许的.
