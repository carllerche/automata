(ns automata.core
  (:refer-clojure :exclude [concat])
  (:use
   clojure.test)
  (:require
   [clojure.set     :as set]
   [clojure.java.io :as io]))

(declare
 find-transition
 ^:dynamic state-counter)

(def epsilon ::epsilon)

(defn- genstate [] (swap! state-counter inc))

(defrecord StateManager
    [automaton
     current-state]
  clojure.lang.IFn
  (invoke [this input]
    (let [state @(.current-state this)]
      (if-let [transition (find-transition (.automaton this) state input)]
        (reset! (.current-state this) (transition :to))
        (throw (Exception. (str "No transition from current state with input: " input))))
      this)))

(defrecord Automaton
    [states      ;; Set of states
     alphabet    ;; The automaton's alphabet
     transitions ;; A set of transitions
     start       ;; The star states
     final]      ;; A set of final states

  clojure.lang.IFn
  (invoke [this]
    (StateManager. this (atom (.start this)))))

(defn- final-states
  [automaton]
  (.final automaton))

(defn- nonfinal-states
  [automaton]
  (set/difference (.states automaton) (.final automaton)))

(defn- transitions-from
  [automaton state input]
  (filter
   #(and (= state (% :from)) (= input (% :input)))
   (.transitions automaton)))

(defn- intersects?
  [a b]
  (seq (set/intersection a b)))

(defn- mk-transition
  [from to input]
  {:from from :to to :input input})

(defn- mk-e-transition
  [from to]
  {:from from :to to :input epsilon})

(defn- basic-automaton
  [input]
  (let [s1 (genstate)
        s2 (genstate)]
    (Automaton.
     #{s1 s2}
     #{input}
     #{(mk-transition s1 s2 input)}
     s1
     #{s2})))

(defn- assoc-conj
  ([map key val]
     (assoc map key (conj (get map key) val)))
  ([map key val & kvs]
     (let [ret (assoc-conj map key val)]
       (if kvs
         (recur ret (first kvs) (second kvs) (nnext kvs))
         ret))))

;;
;; ==== GraphViz file generation
;;

(defn- dot-edges
  [automaton]
  (map
   (fn [{:keys [from to input]}]
     (format "%s -> %s [ label = \"%s\" ];\n" from to input))
   (.transitions automaton)))

(defn- gendot
  [automaton]
  (str "digraph finite_state_machine {\n"
       "rankdir=LR;"
       "size=\"8,5\"\n"
       "node [shape = doublecircle];\n"
       (apply str (map #(str " " %) (.final automaton)))
       ";\nnode [shape = circle];\n"
       (apply str (dot-edges automaton))
       "}\n"))

(defn write-dot
  [automaton dest]
  (with-open [writer (io/writer dest)]
    (.write writer (gendot automaton))))

;;
;; ==== NFA to DFA conversions
;;

(defn- reachable
  "Returns the set of states that are reachable from the given states
  via exactly one transition of specified input or nil if there are
  none."
  [nfa states input]
  (let [ret (->>
             (.transitions nfa)
             (filter #(and (contains? states (get % :from)) (= input (get % :input))))
             (map #(get % :to))
             distinct)]
    (and (seq ret) (apply hash-set ret))))

(defn- epsilon-closure
  "Returns the set of states that are reachable from the given states
  via any number of epsilon transitions."
  [nfa states]
  ;; The argument states are always reachable via 0 transitions, so
  ;; add them to the result set. Add the argument sets to the list of
  ;; remaining states to traverse.
  ;;
  ;; This is a graph traversal.
  (loop [[states remaining] [states (seq states)]]
    (if remaining
      (recur
       ;; For each state, find all other states that are reachable via
       ;; a single epsilon transition. Add all states that have not
       ;; already been traversed to the result set as well as the list
       ;; of unhandled states and recur.
       (loop [states    states
              dests     (seq (reachable nfa #{(first remaining)} epsilon))
              remaining (next remaining)]
         (if (nil? dests)
           [states remaining]
           (recur
            (conj states (first dests))
            (next dests)
            (if (contains? states (first dests))
              remaining (conj remaining (first dests)))))))
      states)))

(defn- conj-remaining-nfa-states
  [dfa nfa]
  (let [[current & unhandled] (get dfa :unhandled)]
    (if current
      (recur
       (reduce
        (fn [dfa input]
          (let [state (epsilon-closure nfa (reachable nfa current input))
                transition (mk-transition current state input)]
            (cond
             (nil? state)
             dfa

             (contains? (.states dfa) state)
             (assoc-conj dfa :transitions transition)

             :else
             (assoc-conj
              dfa
              :transitions transition
              :states      state
              :unhandled   state))))

        (assoc dfa :unhandled unhandled)
        (.alphabet dfa))
       nfa)
      ;; Otherwise, return the build DFA
      (dissoc dfa :unhandled))))

(defn- set-final-states-from-nfa
  [dfa nfa]
  (let [states (filter
                #(seq (set/intersection % (.final nfa)))
                (.states dfa))]
    (assoc dfa :final (apply hash-set states))))

(defn- nfa-to-dfa
  [nfa]
  (let [s1 (epsilon-closure nfa #{(.start nfa)})]
    (-> (Automaton. #{s1} (.alphabet nfa) #{} s1 #{})
        (assoc :unhandled (list s1))
        (conj-remaining-nfa-states nfa)
        (set-final-states-from-nfa nfa))))

;;
;; ==== Normalizing automata
;;

(defn- mk-state-map
  [states]
  ;; (into {} (map-indexed (fn [i state] [state i]) (seq states)))
  (into {} (map (fn [state] [state (genstate)]) (seq states))))

(defn- map-transition
  [state-map {:keys [from to input]}]
  {:from (state-map from) :to (state-map to) :input input})

(defn- normalize
  "Cleans up the naming of the states"
  [automaton]
  (let [state-map (mk-state-map (.states automaton))]
    (Automaton.
     (into #{} (vals state-map))
     (.alphabet automaton)
     (into #{} (map (partial map-transition state-map) (.transitions automaton)))
     (state-map (.start automaton))
     (into #{} (map state-map (seq (.final automaton)))))))

;;
;; ==== DFA minimization
;;

(defn- smallest
  [a b]
  (if (< (count a) (count b))
    a b))

(defn- reaches
  "Returns the set of states for which a transition on the given input
  leads to a state in the given set of destinations."
  [dfa dests input]
  (set
   (filter
    (fn [state]
      (some
       #(contains? dests (% :to))
       (transitions-from dfa state input)))
    (.states dfa))))

(defn- refine-partition
  "Returns the dfa with partition y refined with x."
  [{:keys [remaining partitions] :as dfa} x y]
  (let [a (set/intersection x y)
        b (set/difference y x)]
    (assoc dfa
      :partitions (conj (disj partitions y) a b)
      :remaining
      (if (contains? remaining y)
        (conj (disj remaining y) a b)
        (conj remaining (smallest a b))))))

(defn- refine-partitions
  [{remaining :remaining :as dfa}]
  (if (seq remaining)
    (let [a (first remaining)]
      (recur
       (reduce
        ;; Iterate over each input character and refine the partitions
        (fn [dfa input]
          (let [x (reaches dfa a input)
                partitions (get dfa :partitions)]
            (reduce
             #(refine-partition %1 x %2)
             dfa (filter #(and (not= x %) (intersects? x %)) partitions))))
        (assoc dfa :remaining (disj remaining a))
        (.alphabet dfa))))
    dfa))

(defn- minimized-dfa-from-partitions
  [dfa]
  (let [partitions (get dfa :partitions)
        state-map  #(first (filter (fn [partition] (contains? partition %)) partitions))]
    (Automaton.
     partitions
     (.alphabet dfa)
     (map
      (fn [{:keys [from to input]}]
        {:from (state-map from) :to (state-map to) :input input})
      (.transitions dfa))
     (state-map (.start dfa))
     (filter #(seq (set/intersection % (.final dfa))) partitions))))

(defn- minimize
  [dfa]
  (let [final    (final-states dfa)
        nonfinal (nonfinal-states dfa)]
    (-> dfa
        (assoc :remaining  #{final})
        (assoc :partitions #{final nonfinal})
        (refine-partitions)
        (minimized-dfa-from-partitions)
        (normalize))))

;;
;; ==== Operations
;;

(defn- concat
  ([a] a)
  ([a b]
     (let [epsilons (map #(mk-transition % (.start b) epsilon) (.final a))]
       (minimize
        (nfa-to-dfa
         (Automaton.
          (set/union (.states a) (.states b))
          (set/union (.alphabet a) (.alphabet b))
          (set/union (.transitions a) (.transitions b) epsilons)
          (.start a)
          (.final b))))))
  ([a b & more] (reduce concat (conj more b a))))

(defn- union*
  ([a b]
     (let [s (genstate)
           t #{(mk-transition s (.start a) epsilon)
               (mk-transition s (.start b) epsilon)}]
       (Automaton.
        (set/union (.states a) (.states b) #{s})
        (set/union (.alphabet a) (.alphabet b))
        (set/union (.transitions a) (.transitions b) t)
        s
        (set/union (.final a) (.final b))))))

(defn- union
  ([a] a)
  ([a b] (minimize (nfa-to-dfa (union* a b))))
  ([a b & more] (reduce union (conj more b a))))

(defn- intersection
  ([a] a)
  ([a b]
     (let [unioned (nfa-to-dfa (union* a b))]
       (normalize
        (assoc unioned
          :final
          (filter
           (fn [state]
             (and (seq (set/intersection state (.final a)))
                  (seq (set/intersection state (.final b)))))
           (.final unioned))))))
  ([a b & more] (reduce intersection (conj more b a))))

(defn- kleen
  "Kleen star"
  [a]
  (let [start (genstate)
        final (genstate)]
    (minimize
     (nfa-to-dfa
      (Automaton.
       (set/union (.states a) #{start final})
       (.alphabet a)
       (conj
        (set/union (.transitions a) (map #(mk-e-transition % start) (.final a)))
        (mk-e-transition start (.start a))
        (mk-e-transition start final))
       start
       (set/union (.final a) #{final}))))))

;;
;; ==== Evaluating the automaton
;;

(defn- find-transition
  [automaton from input]
  (first
   (filter
    #(and (= from (% :from)) (= input (% :input)))
    (.transitions automaton))))

(defn final?
  [state-manager]
  (let [state @(.current-state state-manager)]
    (contains?
     (.. state-manager automaton final)
     state)))

;;
;; ==== Defining the automaton
;;

(defn- parse-automaton
  [automaton]
  (if (list? automaton)
    (let [[op & stmts] automaton]
      (cond
       (or (= '| op) (= 'union op))
       (apply union (map parse-automaton stmts))

       (or (= '* op) (= 'kleen op))
       (kleen (apply concat (map parse-automaton stmts)))

       (or (= '& op) (= 'intersection op))
       (apply intersection (map parse-automaton stmts))

       :else
       (throw (Exception. (str "Unknown operator: " op)))))
    (basic-automaton automaton)))

(defn build
  [definitions]
  (binding [state-counter (atom 0)]
    (let [[name part & parts] (first definitions)]
      (loop [res (parse-automaton part) parts parts]
        (if parts
          (recur (concat res (parse-automaton (first parts))) (next parts))
          (normalize res))))))

(defmacro defautomata
  [name & definition]
  `(def ~name (build '~definition)))

(defautomata basic-concat (start :zomg :hi))
(defautomata basic-kleen  (start (* :zomg) :hi2u))
(defautomata basic-union  (start :zomg (union :hi :2u)))

(defautomata basic-intersection
  (start
   (intersection
    (union :foo :bar)
    (union :bar :baz))))

(write-dot basic-intersection "zomg.dot")

(deftest basic-concat-test
  (let [state (basic-concat)]
    (is (not (final? state)))
    (is (state :zomg))
    (is (not (final? state)))
    (is (state :hi))
    (is (final? state))

    (is (thrown? Exception (state :zomg)))
    (is (thrown? Exception (state :hi))))

  ;; Handling errors
  (let [state (basic-concat)]
    (is (thrown? Exception (state :hi)))
    (is (state :zomg))
    (is (thrown? Exception (state :zomg)))))

(deftest basic-kleen-star-test
  (let [state (basic-kleen)]
    (is (not (final? state)))
    (is (state :zomg))
    (is (not (final? state)))
    (is (state :zomg))
    (is (not (final? state)))
    (is (state :hi2u))
    (is (final? state))))

(deftest basic-union-test
  (let [state (basic-union)]
    (is (not (final? state)))
    (is (state :zomg))
    (is (not (final? state)))
    (is (state :hi))
    (is (final? state)))

  (let [state (basic-union)]
    (state :zomg)
    (is (state :2u))
    (is (final? state)))

  ;; Handling errors
  (let [state (basic-union)]
    (state :zomg)
    (is (thrown? Exception (state :zomg)))))

