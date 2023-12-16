(ns explainlib.util
  (:require
   [clojure.core.unify           :as uni]
   [clojure.spec.alpha           :as s]
   [clojure.walk                 :as walk]
   [explainlib.specs             :as specs]
   [mount.core                   :refer [defstate]]
   [taoensso.timbre              :as log]))

(defn combinations-1
  "Create all combinations of elements from the sets, taking one item from each"
  [& sets]
  (reduce (fn [product clause]
            (doall
             (for [p product
                   lit clause]
                (conj p lit))))
          (mapv vector (first sets))
          (rest sets)))

(defn random-index
  "Create a vector of size n using each of the numbers 0 to n-1 once."
  [n]
  (letfn [(pick-from-ref!
            [unu]
            (let [picked (nth @unu (rand-int (count @unu)))]
              (dosync (swap! unu (fn [a] (remove #(= picked %) a))))
              picked))]
    (let [unused (atom (range n))]
      (reduce (fn [v _] (conj v (pick-from-ref! unused)))
              []
              (range n)))))

(defn nspaces
  "Return a string of n spaces."
  [n]
  (reduce (fn [s _] (str s " ")) "" (range n)))

(defn my-abbreviated-output-fn
  "I don't want :hostname_ and :timestamp_ in the log output."
  ([data]       (taoensso.timbre/default-output-fn nil  (dissoc data :hostname_ :timestamp_)))
  ([opts data]  (taoensso.timbre/default-output-fn opts (dissoc data :hostname_ :timestamp_))))

(log/set-config! (assoc log/*config* :output-fn #'my-abbreviated-output-fn))

(defn custom-output-fn
  " - I don't want :hostname_ and :timestamp_ in the log output preface text..
    - I don't want any preface text in rad-mapper.parse output."
  ([data] (custom-output-fn nil data))
  ([opts data]
   (if (=  (:?ns-str data) "rad-mapper.parse")
     (apply str (:vargs data)) ; So it can do simple indented call tracing.
     (taoensso.timbre/default-output-fn opts (dissoc data :hostname_ :timestamp_)))))

(defn fact-not?
  "Return the rest of the proposition (the part without the not) the fact is a factual-not."
  [fact]
  (cond (and (seq? fact) (-> fact meta :factual-not?)) (rest fact)
        (= :fact/not (first fact))
        (throw (ex-info ":fact/not without proper metadata (2):" {:fact fact}))
        :else nil))

(defn unify*
  "uni/unify but with additional provisions when :fact/not."
  [x y]
  (s/assert :specs/proposition x) ; ToDo: only propositions here, right?
  (s/assert :specs/proposition y)
  (let [x* (if (fact-not? x) (rest x) x)
        y* (if (fact-not? y) (rest y) y)]
    (when (or (= :fact/not (first x*)) (= :fact/not (first y*))) ; ToDo: This check is just for development?
      (log/error ":fact/not without proper metadata: x =" x "y =" y)
      (throw (ex-info ":fact/not without proper metadata:" {:x x :y y})))
    (uni/unify x* y*)))

(defn config-log
  "Configure Timbre: set reporting levels and specify a custom :output-fn.
   Return the log/*config*."
  [min-level]
  (if (#{:trace :debug :info :warn :error :fatal :report} min-level)
    (log/set-config!
     (-> log/*config*
         (assoc :output-fn #'custom-output-fn)
         (assoc :min-level [[#{"explainlib.*" "user"} min-level]
                            [#{"*"} :error]])))
    (log/error "Invalid timbre reporting level:" min-level))
  log/*config*)

(defn varize
  "Respectively, add :cvar? and :factual-not? metadata to variables and :fact/not predicates of obj."
  ([obj] (varize obj ""))
  ([obj suffix]
   (letfn [(vize [obj]
             (cond (and (list? obj) (= (first obj) ':fact/not))       (with-meta (conj (map vize (rest obj)) :fact/not) {:factual-not? true}),
                   (and (symbol? obj) (= \? (-> obj name first)))     (with-meta (-> obj name (str suffix) symbol) {:cvar? true})
                   (list? obj)                                        (map vize obj)
                   (vector? obj)                                      (mapv vize obj)
                   (map? obj)                                         (reduce-kv (fn [m k v] (assoc m (vize k) (vize v))) {} obj)
                   :else                                              obj))]
     (vize obj))))

(defn cvar? [x] (-> x meta :cvar?))

(defn collect-vars
  "Return a set of all the vars in a argument form"
  [obj]
  (let [accum (atom #{})]
    (walk/postwalk (fn [x] (when (cvar? x) (swap! accum conj x))) obj)
    @accum))

(defn ground?
  [form]
  (and (seq? form)
       (empty? (collect-vars form))))

;;; ToDo: I'm not quite happy with this design. Metadata on proposition other than :factual-not? could be lost.
;;;       The conundrum is that propositions are simple objects and I'd like to keep them this way.
;;;       Of course, I could search out all the places this is used and store the metadata before the new object is created.
;;;       There are currently 4 places where this is needed.
(defn reapply-fnot-meta
  "meta on fnot propositions is lost when new propositions are made from old ones. This adds it back."
  [obj]
  (letfn [(mb [x]
             (cond (map? x)                                  (reduce-kv (fn [m k v] (assoc m (mb k) (mb v))) {} x)
                   (vector? x)                               (mapv mb x)
                   (and (seq? x) (= :fact/not (first x)))    (with-meta x (assoc (meta x) :factual-not? true))
                   (seq? x)                                  (map mb x)
                   :else                                      x))]
    (mb obj)))

(defstate util
  :start (config-log :info))
