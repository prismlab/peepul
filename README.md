# Certified MRDTs

Certified implmentations of [Mergeable Replicated Data Types](https://dl.acm.org/doi/10.1145/3360580), verified using [F*](https://www.fstar-lang.org/)


Talks and Publications:

Vimala Soundarapandian, KC Sivaramakrishnan, and Kartik Nagar, **Certified Mergeable Replicated Data Types** (PaPoC 2021) [[talk](https://youtu.be/6TTRv5rLI-8)]

List of verified MRDTs:

1. Increment-only counter
2. Enable-wins flag (state : (icounter, flag))
3. Observed-Remove set (state : list (unique ids, elements))
4. Observed-Remove set (state : list (unique ids, unique elements))
5. Observed-Remove set (state : Binary Search Tree with each node being (unique ids, unique elements))
6. Last-Writer-Wins register (state : (timestamp, value))
7. Grows-only set : (state : list (unique elements))
8. Grows-only map composed of Grows-only set : (state : list (unique keys, Gset.state))
9. Functional queue : (state : list (unique ids, elements) × list (unique ids, elements))
10. Functional queue : (state : list (unique ids, elements))
11. Append-only log : (state : list (unique ids, string))
12. Grows-only map composed of Append-only log : (state : list (unique channels, Alog.state))
