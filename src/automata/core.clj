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
;; ==== DFA minimization
;;

(defn- minimize
  [dfa]
  ;; Nothing yet
  dfa)

;;
;; ==== Operations
;;

(defn- concat
  [a b]
  (let [epsilons (map #(mk-transition % (.start b) epsilon) (.final a))]
    (minimize
     (nfa-to-dfa
      (Automaton.
       (set/union (.states a) (.states b))
       (set/union (.alphabet a) (.alphabet b))
       (set/union (.transitions a) (.transitions b) epsilons)
       (.start a)
       (.final b))))))

(defn- union
  [a b]
  (let [s (genstate)
        t #{(mk-transition s (.start a) epsilon)
            (mk-transition s (.start b) epsilon)}]
    (nfa-to-dfa
     (Automaton.
      (set/union (.states a) (.states b) #{s})
      (set/union (.alphabet a) (.alphabet b))
      (set/union (.transitions a) (.transitions b) t)
      s
      (set/union (.final a) (.final b))))))

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

(defn- mk-state-map
  [states]
  (into {} (map-indexed (fn [i state] [state i]) (seq states))))

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

(defn- parse-automaton
  [automaton]
  (if (list? automaton)
    (let [[op & stmts] automaton]
      (cond
       (= 'union op)
       (apply union (map parse-automaton stmts))

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
          (let [ret (normalize res)]
            (println ret)
            ret))))))

(defmacro defautomata
  [name & definition]
  `(def ~name (build '~definition)))

(defautomata basic-concat (start :zomg :hi))
(defautomata basic-union  (start :zomg (union :hi :2u)))

(write-dot basic-union "zomg.dot")

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
