from dcommon import *
s=rd('TLOpsW')
a=s.index('## §1 高度上的序')
b=s.index('## §2 数据树')
c0=s.index('## §3 $\\Omega$, 加法')
d0=s.index('## §5 折叠')
head=s[:a]
i=head.index('```agda')
head='''# 回灌作高度进入数据树 (一): 动态高度

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [TLOpsW](TLOpsW.lagda.md) 改写. **层是三元 $(r,c,a)$, 读 $\\Omega^2\\cdot r+\\Omega\\cdot c+a$, 三个坐标都是 $A$.** `Gν` 的闭包现在是一行数据: `Ω̇₂ (asuc s) azero azero` 是闭包, 分支 $v\\mapsto(s,v,0)$. 高度的第二坐标 $c$ 是**动态**的: 它可以是链点. 比较 $(r,c)$ 与 $(r',c')$: $r$ 走字面公共上界 (`Hk`), $c$ 走世界 (`D`). 世界的规范形多两个候选: $\\max(u,c_q,t,c_p,a)$.
>
> 三个坐标的第 0 行都按构造子分三行: `asuc`: 回灌闭包; `alim`: ℕ-极限; `azero`: 落到下一个坐标. 没有 `View`.

'''+head[i:]
head=head.replace('open import Data.Unit using (⊤; tt)','open import Data.Unit using (⊤; tt)\nopen import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)')
head=head.replace('import OCF.Align.CumReadCF as C','import OCF.Align.CumReadCF as C\nopen import OCF.Align.NoCumLit using (_≈ᴬ_; z≈; s≈; l≈; ≈ᴬ-refl; ≈ᴬ-sym; ≈ᴬ-trans)')
head=head.replace('open import Data.Empty using (⊥)','open import Data.Empty using (⊥; ⊥-elim)')
head=head.replace('module OCF.Align.TLOpsW','module OCF.Align.TLOpsDW')
sec1='''## §1 高度

`a ◂ b`: 字面严格在下. 高度 `hh r c`. `h ◁ p` 八个构造子: 四个降 $r$ (第二坐标任意: 动态), 四个降 $c$.

```agda
infix 4 _◂_
data _◂_ : A → A → Set where
  zero : ∀ {a} → a ◂ asuc a
  suc  : ∀ {a b} → a ◂ b → a ◂ asuc b
  self : ∀ {f} n → f n ◂ alim f
  lim  : ∀ {a f} n → a ◂ f n → a ◂ alim f

◂-tr : ∀ {a b c} → a ◂ b → b ◂ c → a ◂ c
◂-tr p zero = suc p
◂-tr p (suc q) = suc (◂-tr p q)
◂-tr p (self n) = lim n p
◂-tr p (lim n q) = lim n (◂-tr p q)

◂⊲ : ∀ {a b} → a ◂ b → a ⊲ b
◂⊲ zero = C.suc C.self
◂⊲ (suc q) = C.suc (◂⊲ q)
◂⊲ (self n) = C.lim n C.self
◂⊲ (lim n q) = C.lim n (◂⊲ q)

⊲◂ : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (a ◂ b)
⊲◂ C.self = inj₁ refl
⊲◂ (C.suc P) with ⊲◂ P
... | inj₁ refl = inj₂ zero
... | inj₂ i = inj₂ (suc i)
⊲◂ (C.lim n P) with ⊲◂ P
... | inj₁ refl = inj₂ (self n)
... | inj₂ i = inj₂ (lim n i)

data Acc◂ (a : A) : Set where
  acc : (∀ {b} → b ◂ a → Acc◂ b) → Acc◂ a

acc◂ : ∀ a {b} → b ◂ a → Acc◂ b
acc◂ (asuc a) zero = acc (acc◂ a)
acc◂ (asuc a) (suc i) = acc◂ a i
acc◂ (alim f) (self n) = acc (acc◂ (f n))
acc◂ (alim f) (lim n i) = acc◂ (f n) i

◂-irr : ∀ {a} → a ◂ a → ⊥
◂-irr {a} = go (acc (acc◂ a))
  where
  go : ∀ {a} → Acc◂ a → a ◂ a → ⊥
  go (acc h) i = go (h i) i

record H : Set where
  constructor hh
  field
    rr : A
    cc : A
open H public

data R◁ : A → A → A → A → Set where
  rz    : ∀ {s c′ c} → R◁ s c′ (asuc s) c
  rs    : ∀ {s c′ r c₀ c} → R◁ s c′ r c₀ → R◁ s c′ (asuc r) c
  rself : ∀ {f c′ c} n → R◁ (f n) c′ (alim f) c
  rlim  : ∀ {s c′ f c₀ c} n → R◁ s c′ (f n) c₀ → R◁ s c′ (alim f) c
  cz    : ∀ {r c} → R◁ r c r (asuc c)
  cs    : ∀ {r c′ c} → R◁ r c′ r c → R◁ r c′ r (asuc c)
  cself : ∀ {r f} n → R◁ r (f n) r (alim f)
  clim  : ∀ {r c′ f} n → R◁ r c′ r (f n) → R◁ r c′ r (alim f)

infix 4 _◁_
_◁_ : H → H → Set
h ◁ p = R◁ (rr h) (cc h) (rr p) (cc p)

-- 动态坐标: 降 r 时第二坐标要进世界; 降 c 时它在 p 的第二坐标之下, 不要新证据
dn : ∀ {h p} → h ◁ p → A
dn {h} rz = cc h
dn {h} (rs _) = cc h
dn {h} (rself _) = cc h
dn {h} (rlim _ _) = cc h
dn cz = azero
dn (cs _) = azero
dn (cself _) = azero
dn (clim _ _) = azero

data Vw (h p : H) : Set where
  vr : rr h ◂ rr p → Vw h p
  vc : rr h ≡ rr p → cc h ◂ cc p → Vw h p

vw : ∀ {h p} → h ◁ p → Vw h p
vw rz = vr zero
vw (rs i) with vw i
... | vr a = vr (suc a)
... | vc refl _ = vr zero
vw (rself n) = vr (self n)
vw (rlim n i) with vw i
... | vr a = vr (lim n a)
... | vc refl _ = vr (self n)
vw cz = vc refl zero
vw (cs i) with vw i
... | vr a = vr a
... | vc e b = vc e (suc b)
vw (cself n) = vc refl (self n)
vw (clim n i) with vw i
... | vr a = vr a
... | vc e b = vc e (lim n b)

fr◂ : ∀ {s r c′ c} → s ◂ r → hh s c′ ◁ hh r c
fr◂ zero = rz
fr◂ (suc a) = rs {c₀ = azero} (fr◂ a)
fr◂ (self n) = rself n
fr◂ (lim n a) = rlim {c₀ = azero} n (fr◂ a)

fc◂ : ∀ {r c′ c} → c′ ◂ c → hh r c′ ◁ hh r c
fc◂ zero = cz
fc◂ (suc a) = cs (fc◂ a)
fc◂ (self n) = cself n
fc◂ (lim n a) = clim n (fc◂ a)

◁-tr : ∀ {a b d} → a ◁ b → b ◁ d → a ◁ d
◁-tr {hh _ _} {hh _ _} {hh _ _} i j with vw i | vw j
... | vr x | vr y = fr◂ (◂-tr x y)
... | vr x | vc refl _ = fr◂ x
... | vc refl _ | vr y = fr◂ y
... | vc refl x | vc refl y = fc◂ (◂-tr x y)

D : A → A → A → Set
D x a m = (x ⊲ m) × (a ⊲ m)

D⊲ : ∀ {x a m w} → D x a m → m ⊲ w → D x a w
D⊲ (e , f) q = ⊲-tr e q , ⊲-tr f q

Dₛ : ∀ {x b m} → D x (asuc b) m → D x b m
Dₛ (e , f) = e , ⊲-tr (C.suc C.self) f

Dₗ : ∀ {x f m} n → D x (alim f) m → D x (f n) m
Dₗ n (e , f₁) = e , ⊲-tr (C.lim n C.self) f₁

Dz : ∀ m → D azero azero m
Dz m = z⊲ m , z⊲ m

D≪ : ∀ {x k a m} → k ≪ a → D x a m → D x k m
D≪ r (e , f) = e , ⊲-tr (≪⊲ r) f

-- 降 r 的路径: dn 就是低处的第二坐标
dnr : ∀ {h p m} (j : h ◁ p) → rr h ◂ rr p → dn j ⊲ m → cc h ⊲ m
dnr rz x e = e
dnr (rs _) x e = e
dnr (rself _) x e = e
dnr (rlim _ _) x e = e
dnr cz x e = ⊥-elim (◂-irr x)
dnr (cs _) x e = ⊥-elim (◂-irr x)
dnr (cself _) x e = ⊥-elim (◂-irr x)
dnr (clim _ _) x e = ⊥-elim (◂-irr x)

ch⊲ : ∀ {h p m} (j : h ◁ p) → dn j ⊲ m → cc p ⊲ m → cc h ⊲ m
ch⊲ j e f with vw j
... | vr x = dnr j x e
... | vc _ y = ⊲-tr (◂⊲ y) f

dn⊲ : ∀ {h p m} (i : h ◁ p) → cc h ⊲ m → dn i ⊲ m
dn⊲ rz e = e
dn⊲ (rs _) e = e
dn⊲ (rself _) e = e
dn⊲ (rlim _ _) e = e
dn⊲ {m = m} cz e = z⊲ m
dn⊲ {m = m} (cs _) e = z⊲ m
dn⊲ {m = m} (cself _) e = z⊲ m
dn⊲ {m = m} (clim _ _) e = z⊲ m

dn-fr : ∀ {s r c′ c m} (x : s ◂ r) → c′ ⊲ m → dn (fr◂ {s} {r} {c′} {c} x) ⊲ m
dn-fr zero e = e
dn-fr (suc _) e = e
dn-fr (self _) e = e
dn-fr (lim _ _) e = e

dn-fc : ∀ {r c′ c m} (x : c′ ◂ c) → dn (fc◂ {r} x) ⊲ m
dn-fc {m = m} zero = z⊲ m
dn-fc {m = m} (suc _) = z⊲ m
dn-fc {m = m} (self _) = z⊲ m
dn-fc {m = m} (lim _ _) = z⊲ m

dn-tr : ∀ {a b d m} (i : a ◁ b) (j : b ◁ d) → dn i ⊲ m → dn j ⊲ m → dn (◁-tr i j) ⊲ m
dn-tr {hh _ _} {hh _ _} {hh _ _} i j e f with vw i | vw j
... | vr x | vr y = dn-fr (◂-tr x y) (dnr i x e)
... | vr x | vc refl _ = dn-fr x (dnr i x e)
... | vc refl x₁ | vr y = dn-fr y (⊲-tr (◂⊲ x₁) (dnr j y f))
... | vc refl x | vc refl y = dn-fc (◂-tr x y)

-- 第一坐标的字面公共上界
record Hk (p q : H) : Set where
  constructor hk
  field
    {P} : A
    lP  : Lg P
    pP  : rr p ⊲ P
    qP  : rr q ⊲ P
open Hk public

data Tr (p : H) : H → Set where
  tlt : ∀ {q} → p ◁ q → Tr p q
  tgt : ∀ {q} → q ◁ p → Tr p q
  teq : Tr p p

trC : ∀ {r c c′ m} → c ⊲ m → c′ ⊲ m → Lg m → Tr (hh r c) (hh r c′)
trC a b l with cmpF a b l
... | inj₁ q⊲p with ⊲◂ q⊲p
...   | inj₁ refl = teq
...   | inj₂ i = tgt (fc◂ i)
trC a b l | inj₂ p⊲q with ⊲◂ p⊲q
...   | inj₁ refl = teq
...   | inj₂ i = tlt (fc◂ i)

trH : ∀ {p q m} → Hk p q → cc p ⊲ m → cc q ⊲ m → Lg m → Tr p q
trH {hh _ _} {hh _ _} (hk l a b) e f w with cmpF a b l
... | inj₁ q⊲p with ⊲◂ q⊲p
...   | inj₁ refl = trC e f w
...   | inj₂ i = tgt (fr◂ i)
trH {hh _ _} {hh _ _} (hk l a b) e f w | inj₂ p⊲q with ⊲◂ p⊲q
...   | inj₁ refl = trC e f w
...   | inj₂ i = tlt (fr◂ i)

hk◁ : ∀ {h p q} → h ◁ p → Hk p q → Hk h q
hk◁ j (hk l a b) with vw j
... | vr x = hk l (⊲-tr (◂⊲ x) a) b
... | vc e _ = hk l (subst⊲ e a) b
  where
  subst⊲ : ∀ {x y P} → x ≡ y → y ⊲ P → x ⊲ P
  subst⊲ refl q = q

hkR : ∀ {p q} → Hk p q → Hk p p
hkR (hk l a b) = hk l a a

hkD : ∀ {h p q} → h ◁ p → Hk p q → Hk p h
hkD j (hk l a b) with vw j
... | vr x = hk l a (⊲-tr (◂⊲ x) a)
... | vc e _ = hk l a (subst⊲ e a)
  where
  subst⊲ : ∀ {x y P} → x ≡ y → y ⊲ P → x ⊲ P
  subst⊲ refl q = q

hk₀ : ∀ {p} → Lg (rr p) → Hk p (hh azero azero)
hk₀ {p} l = hk l C.self (z⊲ (rr p))

hkZ : ∀ {p q} → Hk p q → Hk (hh azero azero) q
hkZ (hk {P} l a b) = hk l (z⊲ P) b

lgH : ∀ {p q} → Hk p q → Lg (rr p)
lgH (hk w a b) = lg⊲ a w

hkR′ : ∀ {p q} → Hk p q → Hk q q
hkR′ (hk w a b) = hk w b b

infix 4 _≈ᴴ_
data _≈ᴴ_ : H → H → Set where
  ≈h : ∀ {r c c′} → c ≈ᴬ c′ → hh r c ≈ᴴ hh r c′

ecc : ∀ {p q} → p ≈ᴴ q → cc p ≈ᴬ cc q
ecc (≈h e) = e

err : ∀ {p q} → p ≈ᴴ q → rr p ≡ rr q
err (≈h e) = refl

≈ᴴ-refl : ∀ p → p ≈ᴴ p
≈ᴴ-refl (hh r c) = ≈h (≈ᴬ-refl c)

≈ᴴ-sym : ∀ {p q} → p ≈ᴴ q → q ≈ᴴ p
≈ᴴ-sym (≈h e) = ≈h (≈ᴬ-sym e)

≈ᴴ-trans : ∀ {p q s} → p ≈ᴴ q → q ≈ᴴ s → p ≈ᴴ s
≈ᴴ-trans (≈h e) (≈h d) = ≈h (≈ᴬ-trans e d)
```

'''
sec2=s[b:c0]
# data tree
sec2=sec2.replace('module _ (p : A) (a : A)','module _ (p : H) (a : A)')
sec2=sec2.replace('od : ∀ {u h} (i : h ◁ p) (k : A) → k ≪ u →','od : ∀ {u h} (i : h ◁ p) (k : A) → (dn i ⊲ u) × (k ≪ u) →')
sec2=sec2.replace('oL : ∀ {u h} (i : h ◁ p) (k : A) → k ⊲ u →','oL : ∀ {u h} (i : h ◁ p) (k : A) → D (dn i) k u →')
aa=sec2.index('𝓞  : A → A → A → Set')
bb=sec2.index('outC : ')
sec2=sec2[:aa]+'''𝓞₂  : A → A → A → A → Set
Vs₂ : ∀ r c a {b} → Strict b a → A → Set
Vc₂ : ∀ r c a {b} → b ⊲ a → A → Set
Low₂ : ∀ r c {s c′} → R◁ s c′ r c → A → A → Set
𝓞₂ r c a = O₊ (hh r c) a (Vs₂ r c a) (Low₂ r c)
Vs₂ r c (asuc b) (ss P) u = Vc₂ r c b P u
Vs₂ r c (alim f) (sl n P) u = Vc₂ r c (f n) P u
Vc₂ r c a C.self u = 𝓞₂ r c a u
Vc₂ r c (asuc b) (C.suc P) u = Vc₂ r c b P u
Vc₂ r c (alim f) (C.lim n P) u = Vc₂ r c (f n) P u
Low₂ .(asuc s) c (rz {s} {c′}) k u = 𝓞₂ s c′ k u
Low₂ .(asuc r) c (rs {r = r} {c₀ = c₀} i) k u = Low₂ r c₀ i k u
Low₂ .(alim f) c (rself {f} {c′} n) k u = 𝓞₂ (f n) c′ k u
Low₂ .(alim f) c (rlim {f = f} {c₀ = c₀} n i) k u = Low₂ (f n) c₀ i k u
Low₂ r .(asuc c) (cz {c = c}) k u = 𝓞₂ r c k u
Low₂ r .(asuc c) (cs {c = c} i) k u = Low₂ r c i k u
Low₂ r .(alim f) (cself {f = f} n) k u = 𝓞₂ r (f n) k u
Low₂ r .(alim f) (clim {f = f} n i) k u = Low₂ r (f n) i k u

𝓞 : H → A → A → Set
𝓞 p = 𝓞₂ (rr p) (cc p)

Vs : ∀ p a {b} → Strict b a → A → Set
Vs p = Vs₂ (rr p) (cc p)

Vc : ∀ p a {b} → b ⊲ a → A → Set
Vc p = Vc₂ (rr p) (cc p)

Low : ∀ p {h} → h ◁ p → A → A → Set
Low p {h} i = Low₂ (rr p) (cc p) {rr h} {cc h} i

'''+sec2[bb:]
sec2=repath(sec2)
sec3=s[c0:d0]
a3=sec3.index('Ω̇ : ∀ p a → 𝓞 p a one')
b3=sec3.index('-- 右边元素的层')
sec3=sec3[:a3]+'''Ω̇₂ : ∀ r c a → 𝓞₂ r c a one
Ω̇₂ r c (asuc d) = oi C.zero (λ q g z → oe es z)
Ω̇₂ r c (alim f) = ol (λ n → oe (el n) (Ω̇₂ r c (f n)))
Ω̇₂ r (asuc c) azero = oc (oL cz one (z⊲ one , C.self) (Ω̇₂ r c one)) (λ {v} q g → oL cz v (z⊲ v , C.self) (ow (pos g) g₀ (Ω̇₂ r c v)))
Ω̇₂ r (alim f) azero = ol (λ n → oL (cself n) azero (z⊲ one , z⊲ one) (Ω̇₂ r (f n) azero))
Ω̇₂ azero azero azero = os o0
Ω̇₂ (asuc s) azero azero = oc (oL (rz {c′ = one}) azero (C.self , z⊲ one) (Ω̇₂ s one azero)) (λ {v} q g → oL (rz {c′ = v}) azero (C.self , z⊲ v) (ow (pos g) g₀ (Ω̇₂ s v azero)))
Ω̇₂ (alim f) azero azero = ol (λ n → oL (rself {c′ = azero} n) azero (z⊲ one , z⊲ one) (Ω̇₂ (f n) azero azero))

Ω̇ : ∀ p a → 𝓞 p a one
Ω̇ p a = Ω̇₂ (rr p) (cc p) a

Ω̇at : ∀ p a {v} → Gw v → 𝓞 p a v
Ω̇at p a g = ow (pos g) g₀ (Ω̇ p a)

record Stp′ (m₀ b v : A) : Set where
  no-eta-equality
  pattern
  constructor stp′
  field
    m₁ : A
    g₁ : Gw m₁
    le : m₀ ⊲ m₁
    bm : b ⊲ m₁
    mv₁ : m₁ ⊲ v
    wh : (m₁ ≡ m₀) ⊎ (m₁ ≡ b)
open Stp′

step : ∀ {m₀ b v} → Gw m₀ → Gw v → m₀ ⊲ v → b ⊲ v → Stp′ m₀ b v
step {m₀} {b} g gv p q with cmpF p q (lgw gv)
... | inj₁ b⊲m = stp′ m₀ g C.self b⊲m p (inj₁ refl)
... | inj₂ m⊲b = stp′ b (gw (lg⊲ q (lgw gv)) (⊲-tr (pos g) m⊲b)) m⊲b C.self q (inj₂ refl)

record Mx (u x t y a v : A) : Set where
  constructor mx′
  field
    m   : A
    gm  : Gw m
    um  : u ⊲ m
    tm  : D x t m
    am  : D y a m
    mv  : m ⊲ v

-- max(u, x, t, y, a), 字面
mx : ∀ {u x t y a v} → Gw u → Gw v → u ⊲ v → D x t v → D y a v → Mx u x t y a v
mx gu gv uv (xv , tv) (yv , av) with step gu gv uv xv
... | stp′ m₁ g₁ le₁ b₁ v₁ w₁ with step g₁ gv v₁ tv
... | stp′ m₂ g₂ le₂ b₂ v₂ w₂ with step g₂ gv v₂ yv
... | stp′ m₃ g₃ le₃ b₃ v₃ w₃ with step g₃ gv v₃ av
... | stp′ m₄ g₄ le₄ b₄ v₄ w₄ =
  mx′ m₄ g₄ (⊲-tr le₁ (⊲-tr le₂ (⊲-tr le₃ le₄))) (⊲-tr b₁ (⊲-tr le₂ (⊲-tr le₃ le₄)) , ⊲-tr b₂ (⊲-tr le₃ le₄)) (⊲-tr b₃ le₄ , b₄) v₄

'''+sec3[b3:]
sec3=sec3.replace('data Rel : A → A → A → A → Set where','data Rel : H → A → H → A → Set where')
sec3=sec3.replace('''bw↑ : ∀ {p′ b p a v} (R : Rel p′ b p a) → (b ⊲ v) → bw R ⊲ v
bw↑ {v = v} (sa P) e = z⊲ v
bw↑ (lw i) e = e
''','''bd : ∀ {p′ b p a} → Rel p′ b p a → A
bd (sa P) = azero
bd (lw i) = dn i
''')
sec3=sec3.replace('u′ ⊲ v → bw R ⊲ v → 𝓞 p a v','u′ ⊲ v → D (bd R) (bw R) v → 𝓞 p a v').replace('u′ ⊲ m → bw R ⊲ m → 𝓞 p a m','u′ ⊲ m → D (bd R) (bw R) m → 𝓞 p a m')
sec3=sec3.replace('addL : ∀ {p a p′ h k u₀ u′} → 𝓞 p a u₀ → Gw u₀ → h ◁ p → (j : h ◁ p′) → Low p′ j k u′ → Gw u′ → ∀ m → Gw m → u₀ ⊲ m → u′ ⊲ m → k ⊲ m → 𝓞 p a m','addL : ∀ {p a r′ c′ h₁ h₂ k u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (t : hh h₁ h₂ ◁ p) → (j : hh h₁ h₂ ◁ hh r′ c′) → Low (hh r′ c′) j k u′ → Gw u′ → ∀ m → Gw m → u₀ ⊲ m → u′ ⊲ m → D (dn t) k m → 𝓞 p a m')
sec3=sec3.replace('with mx gu₀ gv u₀v xv bv','with mx gu₀ gv u₀v (z⊲ v , xv) bv')
sec3=sec3.replace('add W gu₀ R x gx v gv u₀v xv bv with','add W gu₀ R x gx v gv u₀v xv bv with')
sec3=sec3.replace('... | mx′ m gm um tm am mv = ow mv gm (add⁰ W gu₀ R x gx m gm um tm am)','... | mx′ m gm um tm am mv = ow mv gm (add⁰ W gu₀ R x gx m gm um (proj₂ tm) am)')
sec3=sec3.replace('C.self (z⊲ v))','C.self (Dz v))').replace('C.self (⊲-tr am q))','C.self (D⊲ am q))')
sec3=sec3.replace('od i k (≪∘ r am) (λ','od i k (proj₁ am , ≪∘ r (proj₂ am)) (λ')
sec3=sec3.replace('od j k (≪∘ r tm) (λ','od j k (⊲-tr (proj₁ r) tm , ≪∘ (proj₂ r) tm) (λ')
sec3=sec3.replace('od (◁-tr j i) k (≪∘ r tm) (λ','od (◁-tr j i) k (dn-tr j i (⊲-tr (proj₁ r) tm) (proj₁ am) , ≪∘ (proj₂ r) tm) (λ')
sec3=sec3.replace('x gx m gm um tm (⊲-tr (C.suc C.self) am)','x gx m gm um tm (Dₛ am)').replace('x gx m gm um tm (⊲-tr (C.lim n C.self) am)','x gx m gm um tm (Dₗ n am)')
sec3=sec3.replace('addL W gu₀ j j x gx m gm um tm (⊲-tr e tm)','addL W gu₀ j j x gx m gm um tm (D⊲ e tm)')
sec3=sec3.replace('addL W gu₀ (◁-tr j i) j x gx m gm um tm (⊲-tr e tm)','addL W gu₀ (◁-tr j i) j x gx m gm um tm (dn-tr j i (⊲-tr (proj₁ e) tm) (proj₁ am) , ⊲-tr (proj₂ e) tm)')
sec3=sec3.replace('g u g C.self C.self (z⊲ u)','g u g C.self C.self (Dz u)')
sec3=repath(sec3)
f=s[d0:]
f=f.replace('t ⊲ v → a ⊲ v → 𝓞 q t v','D (cc q) t v → D (cc p) a v → 𝓞 q t v').replace('t ⊲ m → a ⊲ m → 𝓞 q t m','D (cc q) t m → D (cc p) a m → 𝓞 q t m').replace('t ⊲ m → k ⊲ m → 𝓞 q t m','D (cc q) t m → D (cc h) k m → 𝓞 q t m')
f=f.replace('with trH H\n','with trH H (proj₁ am) (proj₁ tm) (lgw gm)\n')
f=f.replace('with trH (hk◁ j H)\n','with trH (hk◁ j H) (Hc j r um am) (proj₁ tm) (lgw gm)\n')
f=f.replace('od i k (≪∘ r am) (λ','od i k (dn⊲ i (proj₁ am) , ≪∘ r (proj₂ am)) (λ')
f=f.replace('od i k (≪∘ r um) (λ','od i k (dn⊲ i (Hc j r um am) , ≪∘ (proj₂ r) um) (λ')
f=f.replace('(⊲-tr tm w) (⊲-tr am w)','(D⊲ tm w) (D⊲ am w)')
f=f.replace('(⊲-tr (≪⊲ r) am) am)','(D≪ r am) am)')
f=f.replace('(⊲-tr (≪⊲ r) um) am)','(Dd j r um am) am)')
f=f.replace('with cmpN (≪∘ r am) tm (lgw gm)','with cmpN (≪∘ r (proj₂ am)) (proj₂ tm) (lgw gm)')
f=f.replace('with cmpN (≪∘ r um) tm (lgw gm)','with cmpN (≪∘ (proj₂ r) um) (proj₂ tm) (lgw gm)')
f=f.replace('tm (⊲-tr (C.suc C.self) am)','tm (Dₛ am)').replace('tm (⊲-tr (C.lim n C.self) am)','tm (Dₗ n am)')
f=f.replace('ψL q t (hk◁ j H) j x gu m gm um tm (⊲-tr e um)','ψL q t (hk◁ j H) j x gu m gm um tm (Dl j e um am)')
f=repath(f)
f=f.replace('''Tᴰ : ∀ p a u₀ → Lg p → Gw u₀ → a ⊲ u₀ → 𝓞 azero azero u₀
Tᴰ p a u₀ lp g e = ψ azero azero (hk₀ lp) (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e''','''hz : H
hz = hh azero azero

Tᴰ : ∀ p a u₀ → Lg (rr p) → Gw u₀ → D (cc p) a u₀ → 𝓞 hz azero u₀
Tᴰ p a u₀ lp g e = ψ hz azero (hk₀ lp) (Ω̇ p a) g₀ u₀ g (pos g) (Dz u₀) e''')
helpers='''```agda
Hc : ∀ {h p k u m a} (j : h ◁ p) → (dn j ⊲ u) × (k ≪ u) → u ⊲ m → D (cc p) a m → cc h ⊲ m
Hc j r um am = ch⊲ j (⊲-tr (proj₁ r) um) (proj₁ am)

Dd : ∀ {h p k u m a} (j : h ◁ p) → (dn j ⊲ u) × (k ≪ u) → u ⊲ m → D (cc p) a m → D (cc h) k m
Dd j r um am = Hc j r um am , ⊲-tr (≪⊲ (proj₂ r)) um

Dl : ∀ {h p k u m a} (j : h ◁ p) → D (dn j) k u → u ⊲ m → D (cc p) a m → D (cc h) k m
Dl j e um am = ch⊲ j (⊲-tr (proj₁ e) um) (proj₁ am) , ⊲-tr (proj₂ e) um
```

'''
s=head+sec1+sec2+sec3+helpers+f
s=s.replace('C.lim 1 ','C.lim 1 ')
# 终止度量: 被加/被折叠元素的高度拆成两列 (r, c), 字典序才看得见
s=s.replace('add  : ∀ {p a p′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel p′ b p a) → 𝓞 p′ b u′','add  : ∀ {p a r′ c′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel (hh r′ c′) b p a) → 𝓞 (hh r′ c′) b u′')
s=s.replace('add⁰ : ∀ {p a p′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel p′ b p a) → 𝓞 p′ b u′','add⁰ : ∀ {p a r′ c′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel (hh r′ c′) b p a) → 𝓞 (hh r′ c′) b u′')
s=s.replace('ψ  : ∀ {p a u} q t → Hk p q → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → D (cc q) t v → D (cc p) a v','ψ  : ∀ {pr pc a u} q t → Hk (hh pr pc) q → 𝓞 (hh pr pc) a u → Gw u → ∀ v → Gw v → u ⊲ v → D (cc q) t v → D pc a v')
s=s.replace('ψᵐ : ∀ {p a u} q t → Hk p q → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → D (cc q) t v → D (cc p) a v','ψᵐ : ∀ {pr pc a u} q t → Hk (hh pr pc) q → 𝓞 (hh pr pc) a u → Gw u → ∀ v → Gw v → u ⊲ v → D (cc q) t v → D pc a v')
s=s.replace('ψ⁰ : ∀ {p a u} q t → Hk p q → 𝓞 p a u → Gw u → ∀ m → Gw m → u ⊲ m → D (cc q) t m → D (cc p) a m','ψ⁰ : ∀ {pr pc a u} q t → Hk (hh pr pc) q → 𝓞 (hh pr pc) a u → Gw u → ∀ m → Gw m → u ⊲ m → D (cc q) t m → D pc a m')
s=s.replace('ψ⁰ {p} {a} q t H (oi {k = k} r h)','ψ⁰ {pr} {pc} {a} q t H (oi {k = k} r h)')
s=s.replace('ψ⁰ {p} {a} q t H (od {h = h₀} j k r h)','ψ⁰ {pr} {pc} {a} q t H (od {h = h₀} j k r h)')
s=s.replace('ψ p k (hkR H)','ψ (hh pr pc) k (hkR H)')
s=s.replace('ψL : ∀ {p h k u} q t → Hk h q → (j : h ◁ p) → Low p j k u → Gw u → ∀ m → Gw m → u ⊲ m → D (cc q) t m → D (cc h) k m → 𝓞 q t m','ψL : ∀ {pr pc h₁ h₂ k u} q t → Hk (hh h₁ h₂) q → (j : hh h₁ h₂ ◁ hh pr pc) → Low (hh pr pc) j k u → Gw u → ∀ m → Gw m → u ⊲ m → D (cc q) t m → D h₂ k m → 𝓞 q t m')
wr('TLOpsDW',mods(s))
