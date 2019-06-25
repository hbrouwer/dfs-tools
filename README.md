# DFS Tools

## About

This implements the **Distributional Formal Semantics (DFS)** framework, as described in:

* [Venhuizen, N. J., Hendriks, P., Crocker, M. W., and Brouwer, H. (2019). A
  Framework for Distributional Formal Semantics. In: Iemhoff, R., Moortgat,
  M., and de Queiroz, R. (Eds.), *Logic, Language, Information, and
  Computation*, Proceedings of the 26th International Workshop WoLLIC 2019,
  LNCS 11541, pp. 633-646. doi:
  10.1007/978-3-662-59533-6_39](https://link.springer.com/chapter/10.1007/978-3-662-59533-6_39)
  [[PDF]](http://njvenhuizen.github.io/pub/venhuizen2019framework.pdf)
  (please cite this paper for DFS Tools)

DFS Tools is written in Prolog, and tested in
[SWI-Prolog](http://www.swi-prolog.org/) and
[YAP](https://www.dcc.fc.up.pt/~vsc/yap/).

Detailed documentation can be found here:

* [DFS Tools PlDoc documentation.](https://hbrouwer.github.io/dfs-tools/)

Examples can be found in the `worlds/` folder.

For more work, employing (an earlier formulation of) the framework, see:

* [Venhuizen, N. J., Crocker, M. W., and Brouwer, H. (2019). Expectation-based Comprehension: Modeling the interaction of world knowledge and linguistic experience. *Discourse Processes, 56:3*, pp. 229-255. doi: 10.1080/0163853X.2018.1448677](https://www.tandfonline.com/doi/full/10.1080/0163853X.2018.1448677)

* [Brouwer, H., Crocker, M. W., and Venhuizen, N. J. (2017). Neural Semantics. In: Wieling, M., Kroon, M., Van Noord, G., and Bouma, G. (eds.), *From Semantics to Dialectometry: Festschrift for John Nerbonne*, pp. 75-83. College Publications.](http://hbrouwer.github.io/papers/Brouwer2017NeuralSemantics.pdf)

## Example workflow

### Sampling:

Sampling a single model:

```prolog
?- dfs_sample_model(M), dfs_pprint_model(M).

%%%% Um = { e1, e2, e3, e4, e5, e6, e7, e8 }
%%%%
%%%% Vm ( john ) = e1
%%%% Vm ( ellen ) = e2
%%%% Vm ( restaurant ) = e3
%%%% Vm ( bar ) = e4
%%%% Vm ( pizza ) = e5
%%%% Vm ( fries ) = e6
%%%% Vm ( wine ) = e7
%%%% Vm ( beer ) = e8
%%%%
%%%% Vm ( order ) = { < e1, e5 >, < e2, e7 >, < e2, e6 >, < e1, e8 >, < e2, e5 > }
%%%% Vm ( pay ) = { e1 }
%%%% Vm ( ask_menu ) = { e2 }
%%%% Vm ( eat ) = { < e2, e5 >, < e2, e6 > }
%%%% Vm ( drink ) = { < e1, e8 > }
%%%% Vm ( enter ) = { < e1, e3 >, < e2, e3 > }
%%%% Vm ( leave ) = { e1 }

M =  ([e1, e2, e3, e4, e5, e6, e7, e8], [john=e1, ellen=e2, restaurant=e3, bar=e4, pizza=e5, fries=e6, wine=e7, ... = ...|...]).
```

Sampling a set of models:

```prolog
?- dfs_sample_models(2,Ms).
Sample: 1 / 2

%%%% drink: { < john, wine >, < ellen, wine > }
%%%% order: { < ellen, wine >, < john, beer >, < john, pizza >, < john, wine >, < ellen, pizza > }
%%%% pay: { ellen, john }
%%%% ask_menu: { ellen }
%%%% enter: { < john, bar >, < ellen, restaurant > }
%%%% eat: { < ellen, pizza > }

Sample: 2 / 2

%%%% pay: { john, ellen }
%%%% enter: { < ellen, bar > }
%%%% order: { < ellen, beer >, < john, beer >, < john, pizza > }
%%%% leave: { ellen, john }
%%%% eat: { < john, pizza > }
%%%% drink: { < ellen, beer > }

Ms = [([e1, e2, e3, e4, e5, e6, e7|...], [john=e1, ellen=e2, restaurant=e3, bar=e4, pizza=e5, fries=e6, ... = ...|...]),  ([e1, e2, e3, e4, e5, e6|...], [john=e1, ellen=e2, restaurant=e3, bar=e4, pizza=e5, ... = ...|...])].
```

### From models to vector space

```prolog
dfs_sample_models(50,Ms), dfs_models_to_matrix(Ms,Mx), dfs_pprint_matrix(Mx).

[...]

%%%% 01011000110110001111111111000101101100100011100011 ask_menu(ellen)
%%%% 01000111000100111010110010100111110101100101001100 ask_menu(john)
%%%% 00001101110000000100000111000100001010001001100000 leave(ellen)
%%%% 10010101001101000100011010010010000100100011000101 leave(john)
%%%% 00111101111111000111100111001110010110111101100000 pay(ellen)
%%%% 10011111001011010101011011010010001010110011001111 pay(john)
%%%% 00000000000101011000100000001001001000110000001010 drink(ellen,beer)
%%%% 11001011111010100101111111011100010110110101111000 drink(ellen,wine)
%%%% 10111111101011100011111010111111000010101010011011 drink(john,beer)
%%%% 00000010101010000100100000010101001001000000101111 drink(john,wine)
%%%% 10001011001010001101110010110010001001100011000001 eat(ellen,fries)
%%%% 00101000100100001000101110010100011000111111001101 eat(ellen,pizza)
%%%% 11100000110011000101010011010100110110101101001001 eat(john,fries)
%%%% 00000100101011001110000101000010001100110010011100 eat(john,pizza)
%%%% 10000001000010001011010001000010110000100000100100 enter(ellen,bar)
%%%% 01110100100101000100001000101101001110011101001011 enter(ellen,restaurant)
%%%% 00001101000010010100000001001100000001101010000001 enter(john,bar)
%%%% 01100010001100001011100110100011001100000001000110 enter(john,restaurant)
%%%% 00000000000101011100100000001001001001110000001010 order(ellen,beer)
%%%% 10001011001010001111110010110010111001100011100001 order(ellen,fries)
%%%% 01101100110100001000101111111100011100111111001101 order(ellen,pizza)
%%%% 11111011111011101111111111011100110111111101111001 order(ellen,wine)
%%%% 11111111111011111011111111111111101011101011011111 order(john,beer)
%%%% 11100000110011110111011011011101110111101111001001 order(john,fries)
%%%% 01100100101011001110100111110011001100110011111111 order(john,pizza)
%%%% 00000010101010001100101000010101011011001011101111 order(john,wine)

Ms = [([e1, e2, e3, e4, e5, e6, e7|...], [john=e1, ellen=e2, restaurant=e3, bar=e4, pizza=e5, fries=e6, ... = ...|...]),  ([e1, e2, e3, e4, e5, e6|...], [john=e1, ellen=e2, restaurant=e3, bar=e4, pizza=e5, ... = ...|...]),  ([e1, e2, e3, e4, e5|...], [john=e1, ellen=e2, restaurant=e3, bar=e4, ... = ...|...]),  ([e1, e2, e3, e4|...], [john=e1, ellen=e2, restaurant=e3, ... = ...|...]),  ([e1, e2, e3|...], [john=e1, ellen=e2, ... = ...|...]),  ([e1, e2|...], [john=e1, ... = ...|...]),  ([e1|...], [... = ...|...]),  ([...|...], [...|...]),  (..., ...)|...],
Mx = [[(ask_menu(ellen), 0),  (ask_menu(john), 0),  (leave(ellen), 0),  (leave(john), 1),  (pay(ellen), 0),  (pay(john), 1),  (drink(..., ...), 0),  (..., ...)|...], [(ask_menu(ellen), 1),  (ask_menu(john), 1),  (leave(ellen), 0),  (leave(john), 0),  (pay(ellen), 0),  (pay(...), 0),  (..., ...)|...], [(ask_menu(ellen), 0),  (ask_menu(john), 0),  (leave(ellen), 0),  (leave(john), 0),  (pay(...), 1),  (..., ...)|...], [(ask_menu(ellen), 1),  (ask_menu(john), 0),  (leave(ellen), 0),  (leave(...), 1),  (..., ...)|...], [(ask_menu(ellen), 1),  (ask_menu(john), 0),  (leave(...), 1),  (..., ...)|...], [(ask_menu(ellen), 0),  (ask_menu(...), 1),  (..., ...)|...], [(ask_menu(...), 0),  (..., ...)|...], [(..., ...)|...], [...|...]|...].
```

### And much more ...

See [DFS Tools PlDoc documentation](https://hbrouwer.github.io/dfs-tools/) for more information.

