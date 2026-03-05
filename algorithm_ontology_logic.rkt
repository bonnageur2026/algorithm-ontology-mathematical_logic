#lang racket

;;;============================================================================
;;; RED-BLACK TREE — CLRS Chapter 13
;;; Combining: Algorithm + Ontology + Mathematical Logic
;;;
;;; 1. ONTOLOGY:    Formal domain model via structs, contracts, and type
;;;                 hierarchies — defines WHAT exists and HOW concepts relate.
;;; 2. LOGIC:       Invariants as executable predicates and contracts —
;;;                 defines WHAT MUST BE TRUE at all times.
;;; 3. ALGORITHM:   Insert, rotate, fixup procedures from CLRS —
;;;                 defines HOW to compute while preserving truth.
;;;============================================================================

(require racket/contract)
(require racket/match)

;;;============================================================================
;;; PART 1: ONTOLOGY — The Domain Model
;;;============================================================================
;;; We define the "universe of discourse": what entities exist, their
;;; properties, and the relationships between them.
;;;
;;; Ontological commitments:
;;;   - A Color is either 'red or 'black (exhaustive, disjoint)
;;;   - A Node is either the sentinel NIL or an internal node
;;;   - Every node has: color, key, left, right, parent
;;;   - The tree is identified by its root
;;;   - Keys belong to an ordered domain (real numbers here)
;;;============================================================================

;; ── Color Ontology ──────────────────────────────────────────────────────────
;; Colors form a finite enumeration: exactly two individuals exist.
(define (color? x)
  (or (eq? x 'red) (eq? x 'black)))

;; ── Node Ontology ───────────────────────────────────────────────────────────
;; A node is a composite entity with five attributes.
;; We use mutable structs because CLRS Red-Black Trees are inherently
;; imperative (rotations mutate parent/child pointers).
(struct node
  ([color  #:mutable]   ; color? — the chromatic property
   [key    #:mutable]   ; real?  — the ordering key
   [left   #:mutable]   ; node?  — left-child relation
   [right  #:mutable]   ; node?  — right-child relation
   [parent #:mutable])  ; node?  — parent relation (inverse of child)
  #:transparent)

;; ── Sentinel Ontology ───────────────────────────────────────────────────────
;; NIL is a distinguished individual: the unique "empty" node.
;; Ontologically, it represents the boundary of the tree.
;; By definition, NIL is always black (this is RB-property 3).
(define NIL (node 'black +inf.0 #f #f #f))
(set-node-left!   NIL NIL)
(set-node-right!  NIL NIL)
(set-node-parent! NIL NIL)

(define (nil-node? n) (eq? n NIL))

;; ── Tree Ontology ───────────────────────────────────────────────────────────
;; A Red-Black Tree is identified by its root node.
;; The root is the unique node whose parent is NIL.
(struct rb-tree
  ([root #:mutable])    ; node? — the root of the tree
  #:transparent)

;; Constructor: creates an empty tree (root is NIL)
(define (make-rb-tree)
  (rb-tree NIL))


;;;============================================================================
;;; PART 2: MATHEMATICAL LOGIC — Invariants and Properties
;;;============================================================================
;;; These predicates encode the FIVE Red-Black properties from CLRS as
;;; executable logical formulas. They serve as:
;;;   - Preconditions  (what must hold before an operation)
;;;   - Postconditions (what must hold after an operation)
;;;   - Loop invariants (what holds throughout fixup)
;;;
;;; In first-order logic notation:
;;;   ∀n ∈ Nodes: color(n) ∈ {red, black}           ... Property 1
;;;   color(root) = black                             ... Property 2
;;;   ∀n: leaf(n) → color(n) = black                 ... Property 3
;;;   ∀n: color(n)=red → color(left(n))=black         ... Property 4
;;;               ∧ color(right(n))=black
;;;   ∀n: all paths from n to leaves have same        ... Property 5
;;;       number of black nodes
;;;============================================================================

;; ── Property 1: Every node is either red or black ──────────────────────────
;; ∀n ∈ Nodes(T): color(n) ∈ {red, black}
(define (property-1? n)
  (cond
    [(nil-node? n) (eq? (node-color n) 'black)]
    [else (and (color? (node-color n))
               (property-1? (node-left n))
               (property-1? (node-right n)))]))

;; ── Property 2: The root is black ──────────────────────────────────────────
;; color(root(T)) = black
(define (property-2? T)
  (eq? (node-color (rb-tree-root T)) 'black))

;; ── Property 3: Every leaf (NIL) is black ──────────────────────────────────
;; ∀n: nil(n) → color(n) = black
;; (This is guaranteed by construction of our NIL sentinel)
(define (property-3? n)
  (cond
    [(nil-node? n) (eq? (node-color n) 'black)]
    [else (and (property-3? (node-left n))
               (property-3? (node-right n)))]))

;; ── Property 4: Red nodes have only black children ─────────────────────────
;; ∀n: color(n) = red → color(left(n)) = black ∧ color(right(n)) = black
(define (property-4? n)
  (cond
    [(nil-node? n) #t]
    [else
     (and (if (eq? (node-color n) 'red)
              (and (eq? (node-color (node-left n))  'black)
                   (eq? (node-color (node-right n)) 'black))
              #t)
          (property-4? (node-left n))
          (property-4? (node-right n)))]))

;; ── Property 5: Black-height consistency ───────────────────────────────────
;; ∀n: ∀ paths p1, p2 from n to a leaf:
;;     count-black(p1) = count-black(p2)
(define (black-height n)
  ;; Returns the black-height if consistent, or #f if violated
  (cond
    [(nil-node? n) 1]  ; NIL counts as 1 black node
    [else
     (let ([lh (black-height (node-left n))]
           [rh (black-height (node-right n))])
       (cond
         [(or (not lh) (not rh)) #f]       ; propagate failure
         [(not (= lh rh))        #f]       ; violation!
         [(eq? (node-color n) 'black) (+ lh 1)]
         [else lh]))]))

(define (property-5? n)
  (not (eq? #f (black-height n))))

;; ── Master Theorem: All five properties hold ───────────────────────────────
;; valid-rb-tree?(T) ⟺ P1(T) ∧ P2(T) ∧ P3(T) ∧ P4(T) ∧ P5(T)
(define (valid-rb-tree? T)
  (let ([r (rb-tree-root T)])
    (and (property-1? r)
         (property-2? T)
         (property-3? r)
         (property-4? r)
         (property-5? r))))

;; ── BST Ordering Invariant ─────────────────────────────────────────────────
;; ∀n: (∀x ∈ left-subtree(n): key(x) ≤ key(n))
;;   ∧ (∀x ∈ right-subtree(n): key(x) > key(n))
(define (valid-bst? n [lo -inf.0] [hi +inf.0])
  (cond
    [(nil-node? n) #t]
    [else
     (let ([k (node-key n)])
       (and (<= lo k) (< k hi)
            (valid-bst? (node-left n)  lo k)
            (valid-bst? (node-right n) k  hi)))]))


;;;============================================================================
;;; PART 3: ALGORITHMS — CLRS Procedures
;;;============================================================================
;;; These implement the operational semantics: HOW the tree changes state
;;; while preserving all logical invariants.
;;;============================================================================

;; ── Left Rotation (CLRS p.313) ─────────────────────────────────────────────
;;
;;     x                y
;;    / \              / \
;;   α   y    →      x   γ
;;      / \         / \
;;     β   γ       α   β
;;
;; Precondition:  right(x) ≠ NIL
;; Postcondition: BST property preserved, structure changed
;;
(define (left-rotate! T x)
  ;; Precondition check (logic guarding the algorithm)
  (when (nil-node? (node-right x))
    (error 'left-rotate! "Precondition violated: right child is NIL"))

  (let ([y (node-right x)])
    ;; Turn y's left subtree into x's right subtree
    (set-node-right! x (node-left y))
    (unless (nil-node? (node-left y))
      (set-node-parent! (node-left y) x))

    ;; Link x's parent to y
    (set-node-parent! y (node-parent x))
    (cond
      [(nil-node? (node-parent x))
       (set-rb-tree-root! T y)]
      [(eq? x (node-left (node-parent x)))
       (set-node-left! (node-parent x) y)]
      [else
       (set-node-right! (node-parent x) y)])

    ;; Put x on y's left
    (set-node-left! y x)
    (set-node-parent! x y)))

;; ── Right Rotation (symmetric to left rotation) ────────────────────────────
(define (right-rotate! T y)
  (when (nil-node? (node-left y))
    (error 'right-rotate! "Precondition violated: left child is NIL"))

  (let ([x (node-left y)])
    (set-node-left! y (node-right x))
    (unless (nil-node? (node-right x))
      (set-node-parent! (node-right x) y))

    (set-node-parent! x (node-parent y))
    (cond
      [(nil-node? (node-parent y))
       (set-rb-tree-root! T x)]
      [(eq? y (node-left (node-parent y)))
       (set-node-left! (node-parent y) x)]
      [else
       (set-node-right! (node-parent y) x)])

    (set-node-right! x y)
    (set-node-parent! y x)))

;; ── RB-Insert-Fixup (CLRS p.316) ──────────────────────────────────────────
;; This is where the magic happens: after a naive BST insert (which may
;; violate Property 2 or Property 4), this procedure restores ALL
;; invariants through rotations and recoloring.
;;
;; Loop invariant (from CLRS):
;;   (a) z is red
;;   (b) If z.p is the root, then z.p is black
;;   (c) There is at most one RB violation:
;;       - Property 2: z is the root and z is red, OR
;;       - Property 4: z and z.p are both red
;;
(define (rb-insert-fixup! T z)
  (let loop ([z z])
    (when (eq? (node-color (node-parent z)) 'red)
      ;; z.p is red, so z.p is NOT the root (root is black by P2)
      ;; Therefore z.p.p exists and is black
      (if (eq? (node-parent z)
               (node-left (node-parent (node-parent z))))

          ;; ── Case A: z's parent is a LEFT child ──────────────────
          (let ([uncle (node-right (node-parent (node-parent z)))])
            (cond
              ;; Case 1: Uncle is red → recolor and move up
              [(eq? (node-color uncle) 'red)
               (set-node-color! (node-parent z) 'black)
               (set-node-color! uncle 'black)
               (set-node-color! (node-parent (node-parent z)) 'red)
               (loop (node-parent (node-parent z)))]

              [else
               ;; Case 2: Uncle is black and z is a right child → left-rotate
               (let ([z (if (eq? z (node-right (node-parent z)))
                            (begin
                              (let ([new-z (node-parent z)])
                                (left-rotate! T new-z)
                                new-z))
                            z)])
                 ;; Case 3: Uncle is black and z is a left child → recolor + right-rotate
                 (set-node-color! (node-parent z) 'black)
                 (set-node-color! (node-parent (node-parent z)) 'red)
                 (right-rotate! T (node-parent (node-parent z))))]))

          ;; ── Case B: z's parent is a RIGHT child (symmetric) ─────
          (let ([uncle (node-left (node-parent (node-parent z)))])
            (cond
              [(eq? (node-color uncle) 'red)
               (set-node-color! (node-parent z) 'black)
               (set-node-color! uncle 'black)
               (set-node-color! (node-parent (node-parent z)) 'red)
               (loop (node-parent (node-parent z)))]

              [else
               (let ([z (if (eq? z (node-left (node-parent z)))
                            (begin
                              (let ([new-z (node-parent z)])
                                (right-rotate! T new-z)
                                new-z))
                            z)])
                 (set-node-color! (node-parent z) 'black)
                 (set-node-color! (node-parent (node-parent z)) 'red)
                 (left-rotate! T (node-parent (node-parent z))))])))))

  ;; Restore Property 2: root must be black
  (set-node-color! (rb-tree-root T) 'black))

;; ── RB-Insert (CLRS p.315) ────────────────────────────────────────────────
;; Standard BST insert followed by fixup.
;; Postcondition: valid-rb-tree?(T) ∧ valid-bst?(root(T))
;;
(define (rb-insert! T key)
  ;; Phase 1: Standard BST insertion (Algorithm)
  (let ([z (node 'red key NIL NIL NIL)])  ; New nodes are always red (ontological rule)
    (let loop ([y NIL]
               [x (rb-tree-root T)])
      (cond
        [(nil-node? x)
         ;; Found the insertion point
         (set-node-parent! z y)
         (cond
           [(nil-node? y) (set-rb-tree-root! T z)]   ; Tree was empty
           [(< key (node-key y)) (set-node-left! y z)]
           [else (set-node-right! y z)])

         ;; Phase 2: Restore invariants (Logic guiding Algorithm)
         (rb-insert-fixup! T z)]

        ;; Continue searching
        [(< key (node-key x))
         (loop x (node-left x))]
        [else
         (loop x (node-right x))]))))


;;;============================================================================
;;; PART 4: SEARCH — Querying the Structure
;;;============================================================================

;; ── Search: O(log n) by BST property ──────────────────────────────────────
(define (rb-search T key)
  (let loop ([x (rb-tree-root T)])
    (cond
      [(nil-node? x) #f]
      [(= key (node-key x)) x]
      [(< key (node-key x)) (loop (node-left x))]
      [else (loop (node-right x))])))

;; ── Minimum / Maximum ─────────────────────────────────────────────────────
(define (rb-minimum n)
  (if (nil-node? (node-left n)) n (rb-minimum (node-left n))))

(define (rb-maximum n)
  (if (nil-node? (node-right n)) n (rb-maximum (node-right n))))

;; ── In-order traversal (yields sorted sequence by BST invariant) ──────────
(define (rb-inorder n)
  (if (nil-node? n)
      '()
      (append (rb-inorder (node-left n))
              (list (cons (node-key n) (node-color n)))
              (rb-inorder (node-right n)))))


;;;============================================================================
;;; PART 5: VISUALIZATION — Seeing the Structure
;;;============================================================================

(define (rb-display n [prefix ""] [is-left #t])
  (unless (nil-node? n)
    (printf "~a~a[~a] ~a\n"
            prefix
            (if is-left "├── " "└── ")
            (node-color n)
            (node-key n))
    (let ([new-prefix (string-append prefix (if is-left "│   " "    "))])
      (rb-display (node-left n) new-prefix #t)
      (rb-display (node-right n) new-prefix #f))))

(define (display-tree T)
  (if (nil-node? (rb-tree-root T))
      (printf "(empty tree)\n")
      (begin
        (printf "\n[~a] ~a  ← root\n"
                (node-color (rb-tree-root T))
                (node-key (rb-tree-root T)))
        (let ([r (rb-tree-root T)])
          (rb-display (node-left r) "" #t)
          (rb-display (node-right r) "" #f)))))


;;;============================================================================
;;; PART 6: DEMONSTRATION — The Three Pillars Working Together
;;;============================================================================

(printf "═══════════════════════════════════════════════════════════\n")
(printf "  RED-BLACK TREE: Algorithm + Ontology + Logic\n")
(printf "═══════════════════════════════════════════════════════════\n\n")

;; Create tree (Ontology: instantiate the domain)
(define T (make-rb-tree))

;; Insert elements (Algorithm: procedural transformation)
(define keys '(41 38 31 12 19 8 50 45 60 55 70 3))
(printf "Inserting keys: ~a\n\n" keys)

(for ([k keys])
  (rb-insert! T k)
  ;; After each insertion, VERIFY all logical invariants hold
  ;; (Logic: postcondition checking)
  (unless (valid-rb-tree? T)
    (error 'demo "INVARIANT VIOLATION after inserting ~a!" k))
  (unless (valid-bst? (rb-tree-root T))
    (error 'demo "BST PROPERTY VIOLATED after inserting ~a!" k)))

;; Display the final tree
(printf "── Final Red-Black Tree ──────────────────────────────────\n")
(display-tree T)

;; Show sorted order (guaranteed by BST invariant)
(printf "\n── In-order traversal (sorted by BST invariant) ─────────\n")
(printf "~a\n" (rb-inorder (rb-tree-root T)))

;; Verify all properties explicitly
(printf "\n── Logical Verification ──────────────────────────────────\n")
(printf "Property 1 (every node is red or black):    ~a\n"
        (if (property-1? (rb-tree-root T)) "✓ HOLDS" "✗ VIOLATED"))
(printf "Property 2 (root is black):                 ~a\n"
        (if (property-2? T) "✓ HOLDS" "✗ VIOLATED"))
(printf "Property 3 (leaves are black):              ~a\n"
        (if (property-3? (rb-tree-root T)) "✓ HOLDS" "✗ VIOLATED"))
(printf "Property 4 (red nodes have black children): ~a\n"
        (if (property-4? (rb-tree-root T)) "✓ HOLDS" "✗ VIOLATED"))
(printf "Property 5 (consistent black-height):       ~a\n"
        (if (property-5? (rb-tree-root T)) "✓ HOLDS" "✗ VIOLATED"))
(printf "BST ordering invariant:                     ~a\n"
        (if (valid-bst? (rb-tree-root T)) "✓ HOLDS" "✗ VIOLATED"))
(printf "Black-height of tree:                       ~a\n"
        (black-height (rb-tree-root T)))

;; Search demonstration
(printf "\n── Search (Algorithm guided by BST invariant) ───────────\n")
(for ([k '(19 50 99)])
  (let ([result (rb-search T k)])
    (if result
        (printf "Search(~a) → found, color = ~a\n" k (node-color result))
        (printf "Search(~a) → not found\n" k))))

(printf "\n── Min/Max (O(log n) by balanced-tree guarantee) ────────\n")
(printf "Minimum: ~a\n" (node-key (rb-minimum (rb-tree-root T))))
(printf "Maximum: ~a\n" (node-key (rb-maximum (rb-tree-root T))))

(printf "\n═══════════════════════════════════════════════════════════\n")
(printf "  All invariants maintained across ~a insertions.\n" (length keys))
(printf "  The LOGIC guarantees O(log n) height.\n")
(printf "  The ONTOLOGY gives structure to reason about.\n")
(printf "  The ALGORITHM transforms state while preserving truth.\n")
(printf "═══════════════════════════════════════════════════════════\n")