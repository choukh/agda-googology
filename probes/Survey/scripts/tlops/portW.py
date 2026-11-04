from common import *
s=rd('NoCumW')
s=common(s)
s=s.replace('''# 不累加的世界: 折叠

> 不含记号. 结论写在 [NoCum](NoCum.lagda.md). 层是 $(p,a)$, 目标 $(q,t)$ 的 $t$ 自己是世界的下界, 与 [CumUpW](CumUpW.lagda.md) 同形. **没有链, 没有 `next`, 没有 `⊞`:** 目标 $(0,0)$ 不再特殊, 闭包 `oc` 留在第 $(0,0)$ 层的数据里, 只有计值 ([NoCumForce](NoCumForce.lagda.md)) 才走链. 本文件的导入闭包不含 `CumReadBase`.
''','''# 树的算子语言 (一): 高度也是 $A$

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumW](NoCumW.lagda.md) 改写: **高度 $p$ 从 $\\mathbb N$ 换成字面合法的 $A$.** 层 $(p,a)$ 读作 $\\Omega\\cdot p+a$, $p$ 与 $a$ 用同一个类型. 第 0 行不再分情况读记号: `Ω̇ p azero` 按 $p$ 的三个构造子分三行, 正好是三个算子 (`asuc`: 回灌闭包 `oc`; `alim`: ℕ-极限 `ol`; `azero`: $1$). 层的后继是 $\\Omega$-极限 `oi`.
>
> 比较高度只需要字面公共上界: `Hk p q`. 比较是 `trH`, 它走 `cmpF` 与 `⊲◁`, 答案是字面的 (`teq` 是 $p\\equiv q$). 所以高度上没有全局三歧, 也不要.
''')
s=s.replace('''<◁-tr : ''','')
# 高度路径
s=s.replace('''## §1 高度上的序

```agda
◁-tr : ∀ {a b c} → a ◁ b → b ◁ c → a ◁ c
◁-tr p zero = suc p
◁-tr p (suc q) = suc (◁-tr p q)
''','''## §1 高度上的序

`h ◁ p`: $h$ 字面地严格在 $p$ 之下. 四个构造子, 与 `Ordᶜ` 的 `_◃_` 同形.

```agda
infix 4 _◁_
data _◁_ : A → A → Set where
  zero : ∀ {a} → a ◁ asuc a
  suc  : ∀ {a b} → a ◁ b → a ◁ asuc b
  self : ∀ {f} n → f n ◁ alim f
  lim  : ∀ {a f} n → a ◁ f n → a ◁ alim f

◁-tr : ∀ {a b c} → a ◁ b → b ◁ c → a ◁ c
◁-tr p zero = suc p
◁-tr p (suc q) = suc (◁-tr p q)
◁-tr p (self n) = lim n p
◁-tr p (lim n q) = lim n (◁-tr p q)

◁⊲ : ∀ {a b} → a ◁ b → a ⊲ b
◁⊲ zero = C.suc C.self
◁⊲ (suc q) = C.suc (◁⊲ q)
◁⊲ (self n) = C.lim n C.self
◁⊲ (lim n q) = C.lim n (◁⊲ q)

⊲◁ : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (a ◁ b)
⊲◁ C.self = inj₁ refl
⊲◁ (C.suc P) with ⊲◁ P
... | inj₁ refl = inj₂ zero
... | inj₂ i = inj₂ (suc i)
⊲◁ (C.lim n P) with ⊲◁ P
... | inj₁ refl = inj₂ (self n)
... | inj₂ i = inj₂ (lim n i)

◁∘⊲ : ∀ {a b c} → a ◁ b → b ⊲ c → a ◁ c
◁∘⊲ i C.self = i
◁∘⊲ i (C.suc q) = suc (◁∘⊲ i q)
◁∘⊲ i (C.lim n q) = lim n (◁∘⊲ i q)

-- 字面的公共上界
record Hk (p q : A) : Set where
  constructor hk
  field
    {P} : A
    lP  : Lg P
    pP  : p ⊲ P
    qP  : q ⊲ P
open Hk public

data Tr (p : A) : A → Set where
  tlt : ∀ {q} → p ◁ q → Tr p q
  tgt : ∀ {q} → q ◁ p → Tr p q
  teq : Tr p p

trH : ∀ {p q} → Hk p q → Tr p q
trH (hk l a b) with cmpF a b l
... | inj₁ q⊲p with ⊲◁ q⊲p
...   | inj₁ refl = teq
...   | inj₂ i = tgt i
trH (hk l a b) | inj₂ p⊲q with ⊲◁ p⊲q
...   | inj₁ refl = teq
...   | inj₂ i = tlt i

hk◁ : ∀ {h p q} → h ◁ p → Hk p q → Hk h q
hk◁ j (hk l a b) = hk l (⊲-tr (◁⊲ j) a) b

hkR : ∀ {p q} → Hk p q → Hk p p
hkR (hk l a b) = hk l a a

hkD : ∀ {h p q} → h ◁ p → Hk p q → Hk p h
hkD j (hk l a b) = hk l a (⊲-tr (◁⊲ j) a)

hkZ : ∀ {p q} → Hk p q → Hk azero q
hkZ (hk {P} l a b) = hk l (z⊲ P) b

hk₀ : ∀ {p} → Lg p → Hk p azero
hk₀ {p} l = hk l C.self (z⊲ p)
''')
s=s.replace('module _ (p : ℕ) (a : A)','module _ (p : A) (a : A)')
s=s.replace('𝓞  : ℕ → A → A → Set','𝓞  : A → A → A → Set')
s=s.replace('''Low (suc q) zero k u = 𝓞 q k u
Low (suc q) (suc i) k u = Low q i k u''','''Low (asuc q) zero k u = 𝓞 q k u
Low (asuc q) (suc i) k u = Low q i k u
Low (alim f) (self n) k u = 𝓞 (f n) k u
Low (alim f) (lim n i) k u = Low (f n) i k u''')
s=s.replace('''Ω̇ zero azero = os o0
Ω̇ (suc p) azero = oc (oL zero one C.self (Ω̇ p one)) (λ {v} q g → oL zero v C.self (ow (pos g) g₀ (Ω̇ p v)))''','''Ω̇ azero azero = os o0
Ω̇ (asuc p) azero = oc (oL zero one C.self (Ω̇ p one)) (λ {v} q g → oL zero v C.self (ow (pos g) g₀ (Ω̇ p v)))
Ω̇ (alim f) azero = ol (λ n → oL (self n) azero (z⊲ one) (Ω̇ (f n) azero))''')
s=s.replace('`Ω̇ p a`: 闭的元素, 世界是 $1$. $(p+1,0)$ 是闭包: 第一支 $(p,1)$, 分支 $(p,v)$. 世界 $v$ 就是下标.','`Ω̇ p a`: 闭的元素, 世界是 $1$. $(p+1,0)$ 是闭包: 第一支 $(p,1)$, 分支 $(p,v)$. 世界 $v$ 就是下标. $(\\lim f,0)$ 是 ℕ-极限.')
s=s.replace('data Rel : ℕ → A → ℕ → A → Set where','data Rel : A → A → A → A → Set where')
# fold
a=s.index('ψ  : ∀ {p a u} q t → 𝓞 p a u')
b=s.index('## §6 闭项')
f=s[a:b]
f=f.replace('∀ {p a u} q t → 𝓞 p a u','∀ {p a u} q t → Hk p q → 𝓞 p a u')
f=f.replace('ψL : ∀ {p h k u} q t (j : h ◁ p) →','ψL : ∀ {p h k u} q t → Hk h q → (j : h ◁ p) →')
f=f.replace('''ψ⁰ {p} {a} q t (oi {k = k} r h) gu m gm um tm am with <-dec p q''','XX')
f=re.sub(r'\bψ q t (x|\(h|\(F)',lambda m:'ψ q t H '+m.group(1),f)
f=re.sub(r'^ψ q t x','ψ q t H x',f,flags=re.M)
f=f.replace('ψᵐ q t x gu v gv uv tv av with','ψᵐ q t H x gu v gv uv tv av with')
f=f.replace('ψ q t H x gu v gv uv tv av = ψᵐ q t x gu','ψ q t H x gu v gv uv tv av = ψᵐ q t H x gu')
f=f.replace('ψ⁰ q t x gu m gm','ψ⁰ q t H x gu m gm')
f=re.sub(r'^ψ⁰ q t ','ψ⁰ q t H ',f,flags=re.M)
f=re.sub(r'^ψ⁰ \{p\} \{a\} q t ','ψ⁰ {p} {a} q t H ',f,flags=re.M)
f=f.replace('with ◁-dec p q','with trH H').replace('with ◁-dec h₀ q','with trH (hk◁ j H)')
f=f.replace('... | injᵃ i','... | tlt i').replace('... | injᵇ _','... | tgt _').replace('... | injᶜ refl','... | teq')
f=f.replace('ψ p k (h ','ψ p k (hkR H) (h ').replace('ψ h₀ k (h ','ψ h₀ k (hkD j H) (h ')
f=f.replace('ψL q t j x gu m gm um tm (⊲-tr e um)','ψL q t (hk◁ j H) j x gu m gm um tm (⊲-tr e um)')
f=f.replace('ψ⁰ q t H (oL j k e x) gu m gm um tm am = ψL q t j x','ψ⁰ q t H (oL j k e x) gu m gm um tm am = ψL q t (hk◁ j H) j x')
f=f.replace('ψL q t zero x gu m gm um tm km = ψ q t H x gu m gm um tm km','ψL q t H zero x gu m gm um tm km = ψ q t H x gu m gm um tm km')
f=f.replace('ψL q t (suc j) x gu m gm um tm km = ψL q t j x gu m gm um tm km','ψL q t H (suc j) x gu m gm um tm km = ψL q t H j x gu m gm um tm km')
s=s[:a]+f+s[b:]
s=s.replace('''Tᴰ : ∀ p a u₀ → Gw u₀ → a ⊲ u₀ → 𝓞 zero azero u₀
Tᴰ p a u₀ g e = ψ zero azero (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e''','''Tᴰ : ∀ p a u₀ → Lg p → Gw u₀ → a ⊲ u₀ → 𝓞 azero azero u₀
Tᴰ p a u₀ lp g e = ψ azero azero (hk₀ lp) (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e''')
s=dup_paths(s)
s=s.replace('ψL q t H (self n₉)','ψL q t H (self n₉)')
wr('TLOpsW',s)
