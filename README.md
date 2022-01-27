# Certified MRDTs

Certified implmentations of [Mergeable Replicated Data Types](https://dl.acm.org/doi/10.1145/3360580), verified using [F*](https://www.fstar-lang.org/)


Talks and Publications:

Vimala Soundarapandian, KC Sivaramakrishnan, and Kartik Nagar, **Certified Mergeable Replicated Data Types** (PaPoC 2021) [[talk](https://youtu.be/6TTRv5rLI-8)]

List of verified MRDTs:

1. Increment-only counter
2. Enable-wins flag (state : (icounter, flag))
3. Enable-wins flag (state : unique id)
4. Observed-Remove set (state : list (unique ids, elements))
5. Observed-Remove set (state : list (unique ids, unique elements))
6. Observed-Remove set (state : Binary Search Tree with each node being (unique ids, unique elements))
7. Last-Writer-Wins register (state : (timestamp, value))
8. Grows-only set : (state : list (unique elements))
9. Grows-only map composed of Grows-only set : (state : list (unique keys, Gset.state))
10. Functional queue : (state : list (unique ids, elements) × list (unique ids, elements))
11. Functional queue : (state : list (unique ids, elements))

Composition:
12. Shopping cart with increment-only counter (state : list (unique items, icounter))
13. Shopping cart with PN counter (state : list (unique items, pncounter))
