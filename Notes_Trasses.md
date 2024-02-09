0 := λ s. λ z. z
1 := λ s. λ z. s z
2 := λ s. λ z. s (s z)
3 := λ s. λ z. s (s (s z))
iszero := λ n. n (λ x. False) True
ifthenelse := λ c. λ t. λ. e. c t e
pred := λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u)
[pred := λ n. (λ f. (λ x. (n (λ g. λ h. h (g f)) (λ u. x) (λ u. u))))]
plus := λ m. λ n. λ f. λ x. m f (n f x)
[plus := λ m. λ n. λ s. λ z. m s (n s z)]
mult := λ m. λ n. m (plus n) 0

Z := λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v))
Y := λ f. (λ x. f (x x)) (λ x. f (x x))
T := (λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n))))
fib := Y(T)

T λx.λy.x.
F λx.λy.y.


**CBN**
Y T 1 ->

	Y := λ f. (λ x. f (x x)) (λ x. f (x x))
	T := (λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n))))
	
(λ f. (λ x. f (x x)) (λ x. f (x x))) T 1 ->
(λ x. T (x x)) (λ x. T (x x)) 1 ->
T ((λ x. T (x x)) (λ x. T (x x))) 1 ->

	Q := ((λ x. T (x x)) (λ x. T (x x)))

(λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n)))) Q 1 ->
if (iszero 1) then 1 else (mult 1 (Q (pred 1))) ->

	ifthenelse := λ c. λ t. λ. e. c t e

(λ c. λ t. λ. e. c t e) (iszero 1) 1 (mult 1 (Q (pred 1))) ->
(iszero 1) 1 (mult 1 (Q (pred 1))) ->

	**iszero 1**
	(λ n. n (λ x. False) True) 1 ->
	1 (λ x. False) True ->
	(λ s. λ z. s z) (λ x. False) True ->
	(λ z. (λ x. False) z) True ->
	(λ x. False) True ->
	False
	**iszero 1**

False 1 (mult 1 (Q (pred 1))) ->
(mult 1 (Q (pred 1))) ->

	mult := λ m. λ n. m (plus n) 0
((λ m. λ n. m (plus n) 0) 1 (Q (pred 1))) ->
1 (plus (Q (pred 1))) 0 ->	
	
	1 := λ s. λ z. s z
	
(λ s. λ z. s z) (plus (Q (pred 1))) 0 ->	
(plus (Q (pred 1))) 0 ->

	plus := λ m. λ n. λ f. λ x. m f (n f x)

((λ m. λ n. λ f. λ x. m f (n f x)) (Q (pred 1))) 0 ->
(λ f. λ x. (Q (pred 1)) f ( 0 f x)) ->
**CBN**



**CBV**
	ifthenelse := λ c. λ t. λ. e. c t e False
	T := (λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n))))
	Z := λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v))

Z T 1 ->
(λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v))) T 1 ->
(λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) 1 ->
 T (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) 1 ->

	Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
	T := (λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n))))
	
(λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n)))) Q 1 ->
if (iszero 1) then (λ unused. 1) else (λ unused. mult 1 (Q  (pred 1))) ->

	ifthenelse := λ c. λ t. λ. e. c t e False

(λ c. λ t. λ. e. c t e False) (iszero 1) (λ unused. 1) (λ unused. mult 1 (Q  (pred 1))) ->

	**iszero 1**
	(λ n. n (λ x. False) True) 1 ->
	1 (λ x. False) True ->
	(λ s. λ z. s z) (λ x. False) True ->
	(λ z. (λ x. False) z) True ->
	(λ x. False) True ->
	False
	**iszero 1**

(λ c. λ t. λ. e. c t e False) False (λ unused. 1) (λ unused. mult 1 (Q  (pred 1))) ->
False (λ unused. 1) (λ unused. mult 1 (Q  (pred 1))) False ->
(λ unused. mult 1 (Q  (pred 1))) False ->
(mult 1 (Q  (pred 1))) ->

	mult := (λ m. λ n. m (plus n) 0)

(λ m. λ n. m (plus n) 0) 1 (Q (pred 1)) ->
(λ n. 1 (plus n) 0) (Q (pred 1)) ->

	**(Q (pred 1))**
	        Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
	(λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) (pred 1) ->
	
	        **(pred 1)**
	        pred := (λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        (λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) 1
	        (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        	L := (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        **(pred 1)**
	
	(λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) L ->
	(λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) L ->
	T (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) L ->

	        Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
        	T := (λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n))))

	(λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n)))) Q L ->
	(if (iszero L) then (λ unused. 1) else (λ unused. mult L (Q (pred L)))) ->

	        ifthenelse := λ c. λ t. λ. e. c t e False

	(λ c. λ t. λ e. c t e False) (iszero L) (λ unused. 1) (λ unused. mult L (Q (pred L))) ->

	        **iszero L**
	        	L := (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        (λ n. n (λ x. False) True) (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) ->
	        (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) (λ x. False) True ->
	        1 (λ g. λ h. h (g (λ x. False))) (λ u. True) (λ u. u) ->
	        	1 := λ s. λ z. s z
	        (λ s. λ z. s z) (λ g. λ h. h (g (λ x. False))) (λ u. True) (λ u. u) ->
	        ((λ g. λ h. h (g (λ x. False))) (λ u. True)) (λ u. u) ->
	        (λ h. h ((λ u. True) (λ x. False))) (λ u. u) ->
	        (λ u. u) ((λ u. True) (λ x. False)) ->
	        (λ u. u) (True) ->
	        (True)
	        **iszero L**

	(λ c. λ t. λ e. c t e False) True (λ unused. 1) (λ unused. mult L (Q (pred L)))) ->
	(True (λ unused. 1) (λ unused. mult L (Q (pred L))) False) ->	
	(λ unused. 1) False ->
	1
	**(Q (pred 1))**

(λ n. 1 (plus n) 0) 1 ->
1 (plus 1) 0 ->

	1 := λ s. λ z. s z
	
(λ s. λ z. s z) (plus 1) 0 ->

	**(plus 1)**
	        plus := λ m. λ n. λ f. λ x. m f (n f x)
	(λ m. λ n. λ f. λ x. m f (n f x)) 1 ->
	(λ n. λ f. λ x. 1 f (n f x)) ->
	**(plus 1)**
	
(λ s. λ z. s z) (λ n. λ f. λ x. 1 f (n f x)) 0 ->
(λ n. λ f. λ x. 1 f (n f x)) 0 ->
(λ f. λ x. 1 f (0 f x))
**CBV**



**AO**
	Y := λ f. (λ x. f (x x)) (λ x. f (x x))
	T := (λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n))))
	
Y T 1 ->
(λ f. (λ x. f (x x)) (λ x. f (x x))) T 1 ->
(λ f. f ((λ x. f (x x)) (λ x. f (x x)))) T 1 ->
(λ f. f (f ((λ x. f (x x)) (λ x. f (x x))))) T 1 ->
...
**AO**



**NO**
	Y := λ f. (λ x. f (x x)) (λ x. f (x x))
	T := (λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n))))
	
Y T 1 ->
(λ f. (λ x. f (x x)) (λ x. f (x x))) T 1 ->
(λ x. T (x x)) (λ x. T (x x)) 1 ->
T ((λ x. T (x x)) (λ x. T (x x))) 1 ->

	Q := ((λ x. T (x x)) (λ x. T (x x)))
	T := (λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n))))

(λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n)))) Q 1 ->
(if (iszero 1) then 1 else (mult 1 (Q (pred 1)))) ->

	ifthenelse := λ c. λ t. λ. e. c t e
	
(λ c. λ t. λ e. c t e) (iszero 1) 1 (mult 1 (Q (pred 1)))) ->
(iszero 1) 1 (mult 1 (Q (pred 1)))) ->
False 1 (mult 1 (Q (pred 1)))) ->
(mult 1 (Q (pred 1)))) ->

	mult := (λ m. λ n. m (plus n) 0)
	
(λ m. λ n. m (plus n) 0) 1 (Q (pred 1)) ->
(1 (plus (Q (pred 1))) 0) ->

	1 := λ s. λ z. s z

(λ s. λ z. s z) (plus (Q (pred 1))) 0 ->
(plus (Q (pred 1))) 0 ->

	plus := λ m. λ n. λ f. λ x. m f (n f x)

((λ m. λ n. λ f. λ x. m f (n f x)) (Q (pred 1))) 0 ->
(λ f. λ x. (Q (pred 1)) f ( 0 f x)) ->

	Q := ((λ x. T (x x)) (λ x. T (x x)))

(λ f. λ x. (((λ x. T (x x)) (λ x. T (x x))) (pred 1)) f ( 0 f x)) ->
(λ f. λ x. ((T ((λ x. T (x x)) (λ x. T (x x)))) (pred 1)) f ( 0 f x)) ->

	Q := ((λ x. T (x x)) (λ x. T (x x)))
	T := (λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n))))

(λ f. λ x. (((λ f. λ n. if (iszero n) then 1 else (mult n (f (pred n)))) Q) (pred 1)) f ( 0 f x)) ->
(λ f. λ x. ((λ n. if (iszero n) then 1 else (mult n (Q (pred n)))) (pred 1)) f ( 0 f x)) ->
(λ f. λ x. ( if (iszero (pred 1)) then 1 else (mult (pred 1) (Q (pred (pred 1))))) f ( 0 f x)) ->

	ifthenelse := λ c. λ t. λ. e. c t e

(λ f. λ x. ((λ c. λ t. λ. e. c t e) (iszero (pred 1)) 1 (mult (pred 1) (Q (pred (pred 1))))) f ( 0 f x)) ->
(λ f. λ x. ((iszero (pred 1)) 1 (mult (pred 1) (Q (pred (pred 1))))) f ( 0 f x)) ->

	**(iszero (pred 1))**
	
	        **(pred 1)**
	        	pred := (λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        (λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) 1
	        (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        **(pred 1)**
	        iszero := (λ n. n (λ x. False) True)
	(λ n. n (λ x. False) True) (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) ->
	(λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) (λ x. False) True ->
	1 (λ g. λ h. h (g (λ x. False))) (λ u. True) (λ u. u) ->
        	1 := λ s. λ z. s z
	(λ s. λ z. s z) (λ g. λ h. h (g (λ x. False))) (λ u. True) (λ u. u) ->
	((λ g. λ h. h (g (λ x. False))) (λ u. True)) (λ u. u) ->
	(λ h. h ((λ u. True) (λ x. False))) (λ u. u) ->
	(λ u. u) ((λ u. True) (λ x. False)) ->
	(λ u. u) (True) ->
	(True)
	**(iszero ((pred 1))**
	

(λ f. λ x. (True 1 (mult (pred 1) (Q (pred (pred 1))))) f ( 0 f x)) ->
(λ f. λ x. 1 f ( 0 f x)) ->

	1 := λ s. λ z. s z
	
(λ f. λ x. (λ s. λ z. s z) f ( 0 f x)) ->
(λ f. λ x. f (0 f x))	
**NO**



------------------------------------------------
0 := λ s. λ z. z
1 := λ s. λ z. s z
2 := λ s. λ z. s (s z)
3 := λ s. λ z. s (s (s z))
iszero := λ n. n (λ x. False) True
ifthenelse := λ c. λ t. λ. e. c t e
pred := λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u)
[pred := λ n. (λ f. (λ x. (n (λ g. λ h. h (g f)) (λ u. x) (λ u. u))))]
plus := λ m. λ n. λ f. λ x. m f (n f x)
[plus := λ m. λ n. λ s. λ z. m s (n s z)]
mult := λ m. λ n. m (plus n) 0

Z := (λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v)))
Y := (λ f. (λ x. f (x x)) (λ x. f (x x)))
T := (λ f. λ n. if (iszero n) then 1 else (plus (f (pred n)) (f (pred pred n))))
fib := Y(T)

T λx.λy.x.
F λx.λy.y.


**CBN**
Y T 2 ->
(λ f. (λ x. f (x x)) (λ x. f (x x))) T 2 ->
(λ x. T (x x)) (λ x. T (x x)) 2 ->
T ((λ x. T (x x)) (λ x. T (x x))) 2 ->

	Q := ((λ x. T (x x)) (λ x. T (x x)))
	T := (λ f. λ n. if (iszero n) then 1 else (plus (f (pred n)) (f (pred pred n))))
	
(λ f. λ n. if (iszero n) then 1 else (plus (f (pred n)) (f (pred pred n)))) Q 2 ->
(if (iszero 2) then 1 else (plus (Q (pred 2)) (Q (pred pred 2)))) ->

	ifthenelse := λ c. λ t. λ. e. c t e
	
(λ c. λ t. λ e. c t e) (iszero 2) 1 (plus (Q (pred 2)) (Q (pred pred 2))) ->
(iszero 2) 1 (plus (Q (pred 2)) (Q (pred pred 2))) ->

	**iszero 2**
	(λ n. n (λ x. False) True) 2 ->
	2 (λ x. False) True ->
	(λ s. λ z. s (s z)) (λ x. False) True ->
	((λ x. False) ((λ x. False) True)) ->
	((λ x. False) ((λ x. False) True)) ->
	False
	**iszero 2**

False 1 (plus (Q (pred 2)) (Q (pred pred 2))) ->
(plus (Q (pred 2)) (Q (pred pred 2))) ->

	plus := λ m. λ n. λ f. λ x. m f (n f x)
	
(λ m. λ n. λ f. λ x. m f (n f x)) (Q (pred 2)) (Q (pred pred 2)) ->
(λ f. λ x. (Q (pred 2)) f ((Q (pred pred 2)) f x)) ->
**CBN**



**CBV**
	ifthenelse := λ c. λ t. λ. e. c t e False
	T := (λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. plus (f (pred n)) (f (pred pred n))))
	Z := (λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v)))

Z T 2 ->
(λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v))) T 2 ->
((λ x. T (λ v. x x v)) (λ x. T (λ v. x x v))) 2 ->
(T (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)) 2 ->

	Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
	T := (λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. plus (f (pred n)) (f (pred pred n))))

((λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. plus (f (pred n)) (f (pred pred n)))) Q) 2 ->
(λ n. if (iszero n) then (λ unused. 1) else (λ unused. plus (Q (pred n)) (Q (pred pred n)))) 2 ->
(if (iszero 2) then (λ unused. 1) else (λ unused. plus (Q (pred 2)) (Q (pred pred 2))))->

	ifthenelse := λ c. λ t. λ. e. c t e False
	
((λ c. λ t. λ. e. c t e False) (iszero 2) (λ unused. 1) (λ unused. plus (Q (pred 2)) (Q (pred pred 2))))->

	**iszero 2**
	(λ n. n (λ x. False) True) 2 ->
	2 (λ x. False) True ->
	(λ s. λ z. s (s z)) (λ x. False) True ->
	((λ x. False) ((λ x. False) True)) ->
	((λ x. False) ((λ x. False) True)) ->
	False
	**iszero 2**

False (λ unused. 1) (λ unused. plus (Q (pred 2)) (Q (pred pred 2))) False ->
(λ unused. plus (Q (pred 2)) (Q (pred pred 2))) False ->
(plus (Q (pred 2)) (Q (pred pred 2))) ->

	plus := λ m. λ n. λ f. λ x. m f (n f x)
	
(λ m. λ n. λ f. λ x. m f (n f x)) (Q (pred 2)) (Q (pred pred 2)) ->

	**(Q (pred 2))**
	        Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
	(λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) (pred 2)
	        **(pred 2)**
	        	pred := λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u)
	        (λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) 2
	        (λ f. λ x. 2 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        	L := (λ f. λ x. 2 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        **(pred 2)**
	(λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) L
	(λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) L
	(T (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)) L
	
	        Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
	        T := (λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. plus (f (pred n)) (f (pred pred n))))
	
	((λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. plus (f (pred n)) (f (pred pred n)))) Q) L
	(λ n. if (iszero n) then (λ unused. 1) else (λ unused. plus (Q (pred n)) (Q (pred pred n)))) L
	(if (iszero L) then (λ unused. 1) else (λ unused. plus (Q (pred L)) (Q (pred pred L))))
	
	        ifthenelse := λ c. λ t. λ. e. c t e False
	
	((λ c. λ t. λ. e. c t e False) (iszero L) (λ unused. 1) (λ unused. plus (Q (pred L)) (Q (pred pred L))))
	
	        **(iszero L)**
	        	iszero := λ n. n (λ x. False) True
	        	L := (λ f. λ x. 2 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        (λ n. n (λ x. False) True) (λ f. λ x. 2 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))

	        **(iszero L)**	
	
	**(Q (pred 2))**
	
	
	
	




(λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) 1 ->
 T (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) 1 ->

	Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
	T := (λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n))))
	
(λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n)))) Q 1 ->
if (iszero 1) then (λ unused. 1) else (λ unused. mult 1 (Q  (pred 1))) ->

	ifthenelse := λ c. λ t. λ. e. c t e False

(λ c. λ t. λ. e. c t e False) (iszero 1) (λ unused. 1) (λ unused. mult 1 (Q  (pred 1))) ->

	**iszero 1**
	(λ n. n (λ x. False) True) 1 ->
	1 (λ x. False) True ->
	(λ s. λ z. s z) (λ x. False) True ->
	(λ z. (λ x. False) z) True ->
	(λ x. False) True ->
	False
	**iszero 1**

(λ c. λ t. λ. e. c t e False) False (λ unused. 1) (λ unused. mult 1 (Q  (pred 1))) ->
False (λ unused. 1) (λ unused. mult 1 (Q  (pred 1))) False ->
(λ unused. mult 1 (Q  (pred 1))) False ->
(mult 1 (Q  (pred 1))) ->

	mult := (λ m. λ n. m (plus n) 0)

(λ m. λ n. m (plus n) 0) 1 (Q (pred 1)) ->
(λ n. 1 (plus n) 0) (Q (pred 1)) ->

	**(Q (pred 1))**
	        Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
	(λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) (pred 1) ->
	
	        **(pred 1)**
	        pred := (λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        (λ n. λ f. λ x. n (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) 1
	        (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        	L := (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        **(pred 1)**
	
	(λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) L ->
	(λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) L ->
	T (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v) L ->

	        Q := (λ v. (λ x. T (λ v. x x v)) (λ x. T (λ v. x x v)) v)
        	T := (λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n))))

	(λ f. λ n. if (iszero n) then (λ unused. 1) else (λ unused. mult n (f (pred n)))) Q L ->
	(if (iszero L) then (λ unused. 1) else (λ unused. mult L (Q (pred L)))) ->

	        ifthenelse := λ c. λ t. λ. e. c t e False

	(λ c. λ t. λ e. c t e False) (iszero L) (λ unused. 1) (λ unused. mult L (Q (pred L))) ->

	        **iszero L**
	        	L := (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u))
	        (λ n. n (λ x. False) True) (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) ->
	        (λ f. λ x. 1 (λ g. λ h. h (g f)) (λ u. x) (λ u. u)) (λ x. False) True ->
	        1 (λ g. λ h. h (g (λ x. False))) (λ u. True) (λ u. u) ->
	        	1 := λ s. λ z. s z
	        (λ s. λ z. s z) (λ g. λ h. h (g (λ x. False))) (λ u. True) (λ u. u) ->
	        ((λ g. λ h. h (g (λ x. False))) (λ u. True)) (λ u. u) ->
	        (λ h. h ((λ u. True) (λ x. False))) (λ u. u) ->
	        (λ u. u) ((λ u. True) (λ x. False)) ->
	        (λ u. u) (True) ->
	        (True)
	        **iszero L**

	(λ c. λ t. λ e. c t e False) True (λ unused. 1) (λ unused. mult L (Q (pred L)))) ->
	(True (λ unused. 1) (λ unused. mult L (Q (pred L))) False) ->	
	(λ unused. 1) False ->
	1
	**(Q (pred 1))**

(λ n. 1 (plus n) 0) 1 ->
1 (plus 1) 0 ->

	1 := λ s. λ z. s z
	
(λ s. λ z. s z) (plus 1) 0 ->

	**(plus 1)**
	        plus := λ m. λ n. λ f. λ x. m f (n f x)
	(λ m. λ n. λ f. λ x. m f (n f x)) 1 ->
	(λ n. λ f. λ x. 1 f (n f x)) ->
	**(plus 1)**
	
(λ s. λ z. s z) (λ n. λ f. λ x. 1 f (n f x)) 0 ->
(λ n. λ f. λ x. 1 f (n f x)) 0 ->
(λ f. λ x. 1 f (0 f x))
**CBV**



