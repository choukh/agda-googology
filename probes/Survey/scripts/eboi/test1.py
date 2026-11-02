from eboi import *
O1=Om(ONE);O2=Om(nat(2));W=P(Z,ONE)
Isuc=I+ONE
samples={'p0(L)':P(Z,LAM),'p0(L+1)':P(Z,LAM+ONE),'p0(O[L+1])':P(Z,Om(LAM+ONE)),'p0(I)':P(Z,I),'p0(I+1)':P(Z,I+ONE),'p0(O[I+1])':P(Z,Om(I+ONE)),'p0(O[I+w])':P(Z,Om(I+W)),'pI(1)':L(ONE),'pI(w)':L(W),'pI(O1)':L(O1),'pI(I)':L(I),'pI(O[I+1])':L(Om(I+ONE))}
for k,t in samples.items():
    print(k,cof(t)[0],'NF',isNF(t),'OT',isOT(tau(t)))
    for n in range(3): print('   ',n,show(fsn(t,n)))
