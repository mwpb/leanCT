open string

constant category: Type
constant object: Π C: category, Type
constant hom: Π {C: category}, object C -> object C -> Type
constant comp: Π {C: category} {a b c: object C}, hom a b → hom b c → hom a c
constant e: Π {C: category} x:object C, hom x x
infix * := comp
constant leftId: Π {C: category} (x y: object C) (f: hom x y), e x * f = f
constant rightId: Π {C: category} (x y: object C) (f: hom x y), f * e y = f

variable C:category
variable x:object C
variable y:object C
variable z:object C
variable f:hom x y
variable g:hom y z
variable h:hom y z

#check leftId
#check f*g
#check e
#check f*(e y)

constant left_intro : Π {C: category} {x y z: object C} {f:hom x y} {g h : hom y z}, g=h → f*g = f*h
#check left_intro

variable Hcd : g=h

theorem trivia: f*g = f*h := 
    calc
        f*g = f*h : left_intro Hcd

#check trivia
