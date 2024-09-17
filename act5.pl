% Definición de tiempos verbales
tiempo(presente).
tiempo(pasado).
tiempo(futuro).

% Definición de las personas gramaticales
persona(primera).
persona(segunda).
persona(tercera).

% Definición de los números gramaticales
numero(singular).
numero(plural).

% Definición de la conjugación del verbo "to be"
ser(presente, primera, singular, "am").
ser(presente, segunda, singular, "are").
ser(presente, tercera, singular, "is").
ser(presente, primera, plural, "are").
ser(presente, segunda, plural, "are").
ser(presente, tercera, plural, "are").

ser(pasado, primera, singular, "was").
ser(pasado, segunda, singular, "were").
ser(pasado, tercera, singular, "was").
ser(pasado, primera, plural, "were").
ser(pasado, segunda, plural, "were").
ser(pasado, tercera, plural, "were").

ser(futuro, primera, singular, "will be").
ser(futuro, segunda, singular, "will be").
ser(futuro, tercera, singular, "will be").
ser(futuro, primera, plural, "will be").
ser(futuro, segunda, plural, "will be").
ser(futuro, tercera, plural, "will be").

% Regla para conjugar el verbo "to be"
conjugar_verbo("to be", Tiempo, Persona, Numero, Conjugacion) :- 
    ser(Tiempo, Persona, Numero, Conjugacion).


% fly
% Definición de tiempos verbales
tiempo(presente).
tiempo(pasado).
tiempo(futuro).

% Definición de las personas gramaticales
persona(primera).
persona(segunda).
persona(tercera).

% Definición de los números gramaticales
numero(singular).
numero(plural).

% Definición de la conjugación del verbo "fly"
volar(presente, primera, singular, "fly").
volar(presente, segunda, singular, "fly").
volar(presente, tercera, singular, "flies").
volar(presente, primera, plural, "fly").
volar(presente, segunda, plural, "fly").
volar(presente, tercera, plural, "fly").

volar(pasado, primera, singular, "flew").
volar(pasado, segunda, singular, "flew").
volar(pasado, tercera, singular, "flew").
volar(pasado, primera, plural, "flew").
volar(pasado, segunda, plural, "flew").
volar(pasado, tercera, plural, "flew").

volar(futuro, primera, singular, "will fly").
volar(futuro, segunda, singular, "will fly").
volar(futuro, tercera, singular, "will fly").
volar(futuro, primera, plural, "will fly").
volar(futuro, segunda, plural, "will fly").
volar(futuro, tercera, plural, "will fly").

% Regla para conjugar el verbo "fly"
conjugar_verbo("fly", Tiempo, Persona, Numero, Conjugacion):- 
    volar(Tiempo, Persona, Numero, Conjugacion).
