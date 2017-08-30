This program will take basic logical propositions, and return a truth table for them.

The full list of supported operators is as follows:
- `!P` - Not P
- `P->Q` - P implies Q
- `P&Q` - P and Q
- `P|Q` - P or Q
- `P<->Q` - P if and only if Q
- `[]P` - It is necessary that P
- `<>P` - It is possible that P
- `P = Q` - P is equivalent to Q. This should only be used as the top level operator, as it will not function properly for anything else (nor would it really make sense for it to do so).

As an example, typing:

```
(P->(Q&!R))<->T
```

shows:

```
((P->(Q&!R))<->T)
    P |     Q |     R |     T
----------------------------------------
True  |  True |  True |  True | False
True  |  True |  True | False |  True
True  |  True | False |  True |  True
True  |  True | False | False | False
True  | False |  True |  True | False
True  | False |  True | False |  True
True  | False | False |  True | False
True  | False | False | False |  True
False |  True |  True |  True |  True
False |  True |  True | False | False
False |  True | False |  True |  True
False |  True | False | False | False
False | False |  True |  True |  True
False | False |  True | False | False
False | False | False |  True |  True
False | False | False | False | False
```
