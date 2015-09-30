A : Type
A = ?MA
B : Type
B = ?MB
C : Type
C = ?MC
D : Type
D = ?MD
E : Type
E = ?ME
F : Type
F = ?MF
G : Type
G = ?MG

th1 : A -> B -> C
th1 = ?M1

th2 : D -> E -> A
th2 = ?M2

th3 : F -> G -> B
th3 = ?M3

ax1 : D
ax1 = ?M4

ax2 : E
ax2 = ?M5

ax3 : F
ax3 = ?M6

ax4 : G
ax4 = ?M7


-- Question : After applying th1, we need to produce a proof of both A and B. In order to prove A, we can apply th2. Now, does it asks for a proof of D (expected) or B ?
-- Answer : in Idris 0.9.14 AND 0.9.15 (and earlier versions), we do NOT have the expected behaviour.
my_theorem : C
my_theorem = ?Mgoal