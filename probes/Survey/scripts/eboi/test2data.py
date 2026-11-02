from eboi import *
O1=Om(ONE);O2=Om(nat(2));W=P(Z,ONE)
base=[Z,ONE,nat(2),W,O1,O2,Om(W),Om(O1),P(Z,O1),P(ONE,O1),P(ONE,O2),LAM,LAM+ONE,Om(LAM+ONE),P(LAM,ONE),P(LAM,W),P(LAM,LAM),P(LAM,Om(LAM+ONE)),P(Z,LAM),P(Z,LAM+ONE),P(Z,Om(LAM+ONE)),
I,I+ONE,I+W,I+I,Om(I+ONE),Om(I+nat(2)),Om(I+W),Om(I+O1),P(I,ONE),P(I,W),P(I,I),P(I,Om(I+ONE)),P(I+ONE,ONE),P(I+ONE,Om(I+nat(2))),Om(Om(I+ONE)),
P(Z,I),P(Z,I+ONE),P(Z,Om(I+ONE)),P(Z,Om(I+W)),P(Z,P(I,I)),P(ONE,I),P(ONE,P(nat(2),I)),P(ONE,Om(nat(2))),
L(ONE),L(nat(2)),L(W),L(O1),L(O2),L(LAM),L(LAM+ONE),L(Om(LAM+ONE)),L(L(ONE)),L(I),L(I+ONE),L(I+I),L(Om(I+ONE)),L(Om(I+W)),L(P(I,I)),P(Z,L(ONE)),P(Z,L(W)),P(Z,L(O1)),P(Z,L(I)),Om(L(ONE)+ONE),P(L(ONE),ONE),P(L(I),ONE),Om(LAM),Om(I),P(Z,Om(LAM)),L(P(L(I),ONE))]
pool=base
