(ns automata.core
  (:refer-clojure :exclude [concat])
  (:use
   clojure.set
   clojure.test))

(declare
 ^:dynamic state-counter)

(def epsilon ::epsilon)

(defn- genstate [] (swap! state-counter inc))

(defrecord Automaton
    [states      ;; Set of states
     alphabet    ;; The automaton's alphabet
     transitions ;; A set of transitions
     start       ;; The star states
     final])     ;; A set of final states

(defn- mk-transition
  [from to input]
  {:from from :to to :input input})

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
              dests     (reachable nfa #{(first remaining)} epsilon)
              remaining (next remaining)]
         (if (or (nil? dests) (states (first dests)))
           [states remaining]
           (recur
            (conj states (first dests))
            (conj remaining (first dests))
            (next dests)))))
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
                #(seq (intersection % (.final nfa)))
                (.states dfa))]
    (assoc dfa :final (apply hash-set states))))

(defn- nfa-to-dfa
  [nfa]
  (let [s1 (epsilon-closure nfa #{(.start nfa)})]
    (-> (Automaton. #{s1} (.alphabet nfa) #{} s1 #{})
        (assoc :unhandled (list s1))
        (conj-remaining-nfa-states nfa)
        (set-final-states-from-nfa nfa))))

(defn- concat
  [a b]
  (let [epsilons (map #(mk-transition % (.start b) epsilon) (.final a))]
    (nfa-to-dfa
     (Automaton.
      (union (.states a) (.states b))
      (union (.alphabet a) (.alphabet b))
      (union (.transitions a) (.transitions b) epsilons)
      (.start a)
      (.final b)))))

(defn- build
  [definitions]
  (binding [state-counter (atom 0)]
    (let [[name part & parts] (first definitions)]
      (loop [res (basic-automaton part) parts parts]
        (if parts
          (recur (concat res (basic-automaton (first parts))) (next parts))
          res)))))

(defmacro defautomata
  [name & definition]
  `(def ~name (build '~definition)))

(defn start
  [automaton]
  (.start automaton))

(defn transition
  [automaton from input]
  ;; Stuff
  )

(defautomata basic
  (start :zomg :hi))

(deftest basic-automaton
  (println "GOT: " basic))
