"""
================================================================================
SUITE UNIVERSITARIA DE MATEMÁTICA DISCRETA
Arquitectura Unificada de 7 Módulos en Orden Secuencial Estricto:
  1. Mate Discreta (Inducción Matemática y Demostraciones Formales)
  2. Import tkinter (Combinatoria: Principio de Conteo, Permutaciones, Combinaciones)
  3. Sistema Aritmética (Teoría de Números: Factorización, MCD, División, Euclides)
  4. Sistema de Grafos (Constructor Visual, Lista/Matriz de Adyacencia y Grados)
  5. Grafos (Rutas BFS, Circuitos DFS, Euler, Hamilton e Isomorfismo Exacto)
  6. Grafos Planos, Coloración y Polinomios (Euler, Kuratowski, Welsh-Powell, P(G,k))
  7. Árboles y Recorrido de Árboles (ABB, DFS Rec/Iter, BFS, Balance AVL y N-arios)
================================================================================
"""

from __future__ import annotations
import tkinter as tk
from tkinter import ttk, messagebox
import math
from collections import Counter, deque
from dataclasses import dataclass, field
from itertools import permutations, combinations
from typing import Dict, List, Optional, Set, Tuple, Deque, Generic, TypeVar

T = TypeVar("T")


# ==============================================================================
# NÚCLEOS ALGEBRAICOS Y ESTRUCTURAS DE DATOS (MÓDULOS 6 Y 7)
# ==============================================================================

class PolinomioCromatico:
    """
    Representa un polinomio en la variable 'k': P(k) = c_n*k^n + ... + c_1*k + c_0.
    Almacena los coeficientes en un diccionario {grado: coeficiente}.
    """

    def __init__(self, terminos: Optional[Dict[int, int]] = None) -> None:
        self.coeficientes: Dict[int, int] = {
            grado: coef for grado, coef in (terminos or {}).items() if coef != 0
        }

    @classmethod
    def monomio_k_elevado_a(cls, exponente: int) -> PolinomioCromatico:
        return cls({exponente: 1})

    def __sub__(self, otro: PolinomioCromatico) -> PolinomioCromatico:
        resultado = dict(self.coeficientes)
        for grado, coef in otro.coeficientes.items():
            resultado[grado] = resultado.get(grado, 0) - coef
        return PolinomioCromatico(resultado)

    def evaluar(self, k: int) -> int:
        return sum(coef * (k ** grado) for grado, coef in self.coeficientes.items())

    def __str__(self) -> str:
        if not self.coeficientes:
            return "0"
        partes: List[str] = []
        for grado in sorted(self.coeficientes.keys(), reverse=True):
            coef = self.coeficientes[grado]
            signo = " - " if coef < 0 else (" + " if partes else "")
            valor_abs = abs(coef)

            if grado == 0:
                termino = f"{valor_abs}"
            elif grado == 1:
                termino = "k" if valor_abs == 1 else f"{valor_abs}k"
            else:
                termino = f"k^{grado}" if valor_abs == 1 else f"{valor_abs}k^{grado}"

            if not partes and coef < 0:
                partes.append(f"-{termino}")
            else:
                partes.append(f"{signo}{termino}")
        return "".join(partes)


@dataclass
class ReportePlanaridad:
    es_plano: bool
    vertices: int
    aristas: int
    componentes_conexas: int
    caras_euler: Optional[int]
    motivo: str


@dataclass
class Grafo:
    """Grafo simple no dirigido con soporte para Planaridad, Coloración y P(G, k)."""
    nombre: str
    adyacencia: Dict[str, Set[str]] = field(default_factory=dict)

    def agregar_vertice(self, v: str) -> None:
        if v not in self.adyacencia:
            self.adyacencia[v] = set()

    def agregar_arista(self, u: str, v: str) -> None:
        if u == v:
            return
        self.agregar_vertice(u)
        self.agregar_vertice(v)
        self.adyacencia[u].add(v)
        self.adyacencia[v].add(u)

    def obtener_aristas(self) -> List[Tuple[str, str]]:
        aristas: List[Tuple[str, str]] = []
        visitadas: Set[Tuple[str, str]] = set()
        for u in sorted(self.adyacencia.keys()):
            for v in sorted(self.adyacencia[u]):
                par = (min(u, v), max(u, v))
                if par not in visitadas:
                    visitadas.add(par)
                    aristas.append(par)
        return aristas

    def copiar(self) -> Grafo:
        nuevo = Grafo(self.nombre)
        nuevo.adyacencia = {v: set(vecinos) for v, vecinos in self.adyacencia.items()}
        return nuevo

    def eliminar_arista(self, u: str, v: str) -> Grafo:
        g_nuevo = self.copiar()
        g_nuevo.adyacencia[u].discard(v)
        g_nuevo.adyacencia[v].discard(u)
        return g_nuevo

    def contraer_arista(self, u: str, v: str) -> Grafo:
        g_nuevo = self.copiar()
        vecinos_v = g_nuevo.adyacencia.pop(v, set())
        g_nuevo.adyacencia[u].discard(v)

        for w in vecinos_v:
            g_nuevo.adyacencia[w].discard(v)
            if w != u:
                g_nuevo.adyacencia[u].add(w)
                g_nuevo.adyacencia[w].add(u)
        return g_nuevo

    def polinomio_cromatico(self) -> PolinomioCromatico:
        aristas = self.obtener_aristas()
        if not aristas:
            return PolinomioCromatico.monomio_k_elevado_a(len(self.adyacencia))
        u, v = aristas[0]
        p_elim = self.eliminar_arista(u, v).polinomio_cromatico()
        p_cont = self.contraer_arista(u, v).polinomio_cromatico()
        return p_elim - p_cont

    def _contar_componentes_conexas(self) -> int:
        visitados: Set[str] = set()
        componentes = 0
        for v in self.adyacencia:
            if v not in visitados:
                componentes += 1
                cola = deque([v])
                visitados.add(v)
                while cola:
                    actual = cola.popleft()
                    for vecino in self.adyacencia[actual]:
                        if vecino not in visitados:
                            visitados.add(vecino)
                            cola.append(vecino)
        return componentes

    def _tiene_triangulos(self) -> bool:
        for u in self.adyacencia:
            vecinos_u = self.adyacencia[u]
            for v in vecinos_u:
                if vecinos_u.intersection(self.adyacencia[v]):
                    return True
        return False

    def _reducir_subdivisiones(self) -> Grafo:
        g = self.copiar()
        cambio = True
        while cambio:
            cambio = False
            for v in list(g.adyacencia.keys()):
                grado = len(g.adyacencia[v])
                if grado <= 1:
                    for vecino in list(g.adyacencia[v]):
                        g.adyacencia[vecino].discard(v)
                    del g.adyacencia[v]
                    cambio = True
                elif grado == 2:
                    u, w = list(g.adyacencia[v])
                    del g.adyacencia[v]
                    g.adyacencia[u].discard(v)
                    g.adyacencia[w].discard(v)
                    if u != w:
                        g.adyacencia[u].add(w)
                        g.adyacencia[w].add(u)
                    cambio = True
        return g

    def _contiene_kuratowski(self) -> Optional[str]:
        nucleo = self._reducir_subdivisiones()
        nodos = list(nucleo.adyacencia.keys())

        # 1. Verificación de subgrafo K_5
        if len(nodos) >= 5:
            for sub in combinations(nodos, 5):
                if all(v in nucleo.adyacencia[u] for u, v in combinations(sub, 2)):
                    return f"Contiene una subdivisión homeomórfica de K_5 en {sub} (Teorema de Kuratowski)."

        # 2. Verificación de subgrafo K_{3,3}
        if len(nodos) >= 6:
            for sub in combinations(nodos, 6):
                conjunto_sub = set(sub)
                for part_a in combinations(sub, 3):
                    set_a = set(part_a)
                    set_b = conjunto_sub - set_a
                    if all(b in nucleo.adyacencia[a] for a in set_a for b in set_b):
                        return (
                            f"Contiene una subdivisión homeomórfica de K_{{3,3}} "
                            f"con particiones {sorted(set_a)} y {sorted(set_b)} (Teorema de Kuratowski)."
                        )
        return None

    def analizar_planaridad(self) -> ReportePlanaridad:
        V = len(self.adyacencia)
        E = len(self.obtener_aristas())
        C = self._contar_componentes_conexas() if V > 0 else 0

        if V <= 4:
            caras = E - V + 1 + C if V > 0 else 1
            return ReportePlanaridad(
                True, V, E, C, caras,
                "Todo grafo simple con V <= 4 es trivialmente plano."
            )

        kuratowski = self._contiene_kuratowski()
        if kuratowski:
            return ReportePlanaridad(False, V, E, C, None, kuratowski)

        cota_general = 3 * V - 6
        if E > cota_general:
            return ReportePlanaridad(
                False, V, E, C, None,
                f"Viola el Corolario de Euler: E = {E} > 3V - 6 = {cota_general}."
            )

        if not self._tiene_triangulos() and V >= 3:
            cota_sin_triangulos = 2 * V - 4
            if E > cota_sin_triangulos:
                return ReportePlanaridad(
                    False, V, E, C, None,
                    f"Grafo libre de triángulos viola E <= 2V - 4: E = {E} > {cota_sin_triangulos}."
                )

        # Fórmula de Euler generalizada para C componentes conexas: V - E + F = 1 + C
        caras = E - V + 1 + C
        return ReportePlanaridad(
            True, V, E, C, caras,
            f"Supera las cotas de Euler y está libre de menores de Kuratowski (K_5 y K_{{3,3}})."
        )

    def coloracion_welsh_powell(self) -> Dict[str, int]:
        """Heurística voraz ordenando vértices por grado descendente."""
        orden = sorted(
            self.adyacencia.keys(),
            key=lambda v: (-len(self.adyacencia[v]), v)
        )
        colores: Dict[str, int] = {}
        for v in orden:
            colores_vecinos = {colores[vec] for vec in self.adyacencia[v] if vec in colores}
            c = 1
            while c in colores_vecinos:
                c += 1
            colores[v] = c
        return colores

    def coloracion_exacta(self) -> Tuple[int, Dict[str, int]]:
        """Determina el número cromático exacto chi(G) mediante Backtracking."""
        if not self.adyacencia:
            return 0, {}
        nodos = sorted(
            self.adyacencia.keys(),
            key=lambda v: (-len(self.adyacencia[v]), v)
        )
        n = len(nodos)
        asignacion: Dict[str, int] = {}

        def es_seguro(v: str, c: int) -> bool:
            return all(asignacion.get(vec) != c for vec in self.adyacencia[v])

        def backtrack(idx: int, max_k: int) -> bool:
            if idx == n:
                return True
            v = nodos[idx]
            for c in range(1, max_k + 1):
                if es_seguro(v, c):
                    asignacion[v] = c
                    if backtrack(idx + 1, max_k):
                        return True
                    del asignacion[v]
            return False

        for k in range(1, n + 1):
            asignacion.clear()
            if backtrack(0, k):
                return k, dict(asignacion)
        return n, {v: i + 1 for i, v in enumerate(nodos)}


@dataclass
class NodoBinario(Generic[T]):
    valor: T
    izquierdo: Optional[NodoBinario[T]] = None
    derecho: Optional[NodoBinario[T]] = None


class ArbolBinarioBusqueda(Generic[T]):
    """Árbol Binario de Búsqueda completo (Módulo 7)."""

    def __init__(self) -> None:
        self.raiz: Optional[NodoBinario[T]] = None

    def insertar(self, valor: T) -> None:
        if self.raiz is None:
            self.raiz = NodoBinario(valor)
            return
        actual = self.raiz
        while True:
            if valor < actual.valor:  # type: ignore[operator]
                if actual.izquierdo is None:
                    actual.izquierdo = NodoBinario(valor)
                    return
                actual = actual.izquierdo
            elif valor > actual.valor:  # type: ignore[operator]
                if actual.derecho is None:
                    actual.derecho = NodoBinario(valor)
                    return
                actual = actual.derecho
            else:
                return

    def buscar(self, valor: T) -> Tuple[bool, List[T]]:
        camino: List[T] = []
        actual = self.raiz
        while actual is not None:
            camino.append(actual.valor)
            if valor == actual.valor:
                return True, camino
            elif valor < actual.valor:  # type: ignore[operator]
                actual = actual.izquierdo
            else:
                actual = actual.derecho
        return False, camino

    def eliminar(self, valor: T) -> None:
        self.raiz = self._eliminar_recursivo(self.raiz, valor)

    def _eliminar_recursivo(
        self, nodo: Optional[NodoBinario[T]], valor: T
    ) -> Optional[NodoBinario[T]]:
        if nodo is None:
            return None
        if valor < nodo.valor:  # type: ignore[operator]
            nodo.izquierdo = self._eliminar_recursivo(nodo.izquierdo, valor)
        elif valor > nodo.valor:  # type: ignore[operator]
            nodo.derecho = self._eliminar_recursivo(nodo.derecho, valor)
        else:
            if nodo.izquierdo is None:
                return nodo.derecho
            if nodo.derecho is None:
                return nodo.izquierdo
            sucesor = self._minimo_nodo(nodo.derecho)
            nodo.valor = sucesor.valor
            nodo.derecho = self._eliminar_recursivo(nodo.derecho, sucesor.valor)
        return nodo

    def _minimo_nodo(self, nodo: NodoBinario[T]) -> NodoBinario[T]:
        actual = nodo
        while actual.izquierdo is not None:
            actual = actual.izquierdo
        return actual

    def pre_orden_recursivo(self) -> List[T]:
        resultado: List[T] = []
        def _dfs(n: Optional[NodoBinario[T]]) -> None:
            if n:
                resultado.append(n.valor)
                _dfs(n.izquierdo)
                _dfs(n.derecho)
        _dfs(self.raiz)
        return resultado

    def in_orden_recursivo(self) -> List[T]:
        resultado: List[T] = []
        def _dfs(n: Optional[NodoBinario[T]]) -> None:
            if n:
                _dfs(n.izquierdo)
                resultado.append(n.valor)
                _dfs(n.derecho)
        _dfs(self.raiz)
        return resultado

    def post_orden_recursivo(self) -> List[T]:
        resultado: List[T] = []
        def _dfs(n: Optional[NodoBinario[T]]) -> None:
            if n:
                _dfs(n.izquierdo)
                _dfs(n.derecho)
                resultado.append(n.valor)
        _dfs(self.raiz)
        return resultado

    def pre_orden_iterativo(self) -> List[T]:
        if not self.raiz:
            return []
        resultado: List[T] = []
        pila: List[NodoBinario[T]] = [self.raiz]
        while pila:
            actual = pila.pop()
            resultado.append(actual.valor)
            if actual.derecho:
                pila.append(actual.derecho)
            if actual.izquierdo:
                pila.append(actual.izquierdo)
        return resultado

    def in_orden_iterativo(self) -> List[T]:
        resultado: List[T] = []
        pila: List[NodoBinario[T]] = []
        actual = self.raiz
        while actual or pila:
            while actual:
                pila.append(actual)
                actual = actual.izquierdo
            actual = pila.pop()
            resultado.append(actual.valor)
            actual = actual.derecho
        return resultado

    def post_orden_iterativo(self) -> List[T]:
        if not self.raiz:
            return []
        resultado: List[T] = []
        pila: List[Tuple[NodoBinario[T], bool]] = [(self.raiz, False)]
        while pila:
            nodo, visitado = pila.pop()
            if visitado:
                resultado.append(nodo.valor)
            else:
                pila.append((nodo, True))
                if nodo.derecho:
                    pila.append((nodo.derecho, False))
                if nodo.izquierdo:
                    pila.append((nodo.izquierdo, False))
        return resultado

    def recorrido_por_niveles_bfs(self) -> Tuple[List[T], List[List[T]]]:
        if not self.raiz:
            return [], []
        plano: List[T] = []
        por_niveles: List[List[T]] = []
        cola: Deque[NodoBinario[T]] = deque([self.raiz])
        while cola:
            tamano_nivel = len(cola)
            nivel_actual: List[T] = []
            for _ in range(tamano_nivel):
                nodo = cola.popleft()
                plano.append(nodo.valor)
                nivel_actual.append(nodo.valor)
                if nodo.izquierdo:
                    cola.append(nodo.izquierdo)
                if nodo.derecho:
                    cola.append(nodo.derecho)
            por_niveles.append(nivel_actual)
        return plano, por_niveles

    def altura(self) -> int:
        def _altura(n: Optional[NodoBinario[T]]) -> int:
            if n is None:
                return -1
            return 1 + max(_altura(n.izquierdo), _altura(n.derecho))
        return _altura(self.raiz)

    def obtener_hojas(self) -> List[T]:
        hojas: List[T] = []
        def _buscar(n: Optional[NodoBinario[T]]) -> None:
            if n:
                if n.izquierdo is None and n.derecho is None:
                    hojas.append(n.valor)
                _buscar(n.izquierdo)
                _buscar(n.derecho)
        _buscar(self.raiz)
        return hojas

    def es_balanceado_avl(self) -> bool:
        def _verificar(n: Optional[NodoBinario[T]]) -> Tuple[bool, int]:
            if n is None:
                return True, -1
            b_izq, a_izq = _verificar(n.izquierdo)
            if not b_izq:
                return False, 0
            b_der, a_der = _verificar(n.derecho)
            if not b_der:
                return False, 0
            return abs(a_izq - a_der) <= 1, 1 + max(a_izq, a_der)
        bal, _ = _verificar(self.raiz)
        return bal

    def renderizar_ascii(self) -> str:
        if not self.raiz:
            return "(Árbol vacío)"
        lineas: List[str] = []
        def _dibujar(
            nodo: Optional[NodoBinario[T]], prefijo: str, es_izq: bool, es_raiz: bool
        ) -> None:
            if nodo is None:
                return
            if nodo.derecho:
                nuevo_pref = prefijo + ("│   " if es_izq and not es_raiz else "    ")
                _dibujar(nodo.derecho, nuevo_pref, False, False)
            conector = "Raíz── " if es_raiz else ("└── " if es_izq else "┌── ")
            lineas.append(f"{prefijo}{conector}[{nodo.valor}]")
            if nodo.izquierdo:
                nuevo_pref = prefijo + ("    " if es_izq or es_raiz else "│   ")
                _dibujar(nodo.izquierdo, nuevo_pref, True, False)
        _dibujar(self.raiz, "", False, True)
        return "\n".join(lineas)


@dataclass
class NodoNario(Generic[T]):
    valor: T
    hijos: List[NodoNario[T]] = field(default_factory=list)

    def agregar_hijo(self, hijo: NodoNario[T]) -> NodoNario[T]:
        self.hijos.append(hijo)
        return hijo

    def pre_orden(self) -> List[T]:
        res = [self.valor]
        for h in self.hijos:
            res.extend(h.pre_orden())
        return res

    def post_orden(self) -> List[T]:
        res: List[T] = []
        for h in self.hijos:
            res.extend(h.post_orden())
        res.append(self.valor)
        return res


# ==============================================================================
# MÓDULO 1: MATE DISCRETA (INDUCCIÓN MATEMÁTICA)
# ==============================================================================

class Modulo1MateDiscreta(tk.Frame):
    def __init__(self, parent: tk.Widget) -> None:
        super().__init__(parent, bg="#f8fafc")
        self._construir_ui()

    def _construir_ui(self) -> None:
        header = tk.Label(
            self, text="MÓDULO 1: MATEMÁTICA DISCRETA — INDUCCIÓN MATEMÁTICA",
            font=("Arial", 16, "bold"), bg="#0f172a", fg="white", pady=12
        )
        header.pack(fill="x")

        cuerpo = tk.Frame(self, bg="#f8fafc", padx=16, pady=14)
        cuerpo.pack(fill="both", expand=True)

        panel = tk.Frame(cuerpo, bg="#e2e8f0", padx=14, pady=14, width=310)
        panel.pack(side="left", fill="y")
        panel.pack_propagate(False)

        tk.Label(
            panel, text="Valor de prueba (n ∈ ℕ):",
            font=("Arial", 11, "bold"), bg="#e2e8f0"
        ).pack(anchor="w")
        self.entrada_n = tk.Entry(panel, font=("Arial", 12))
        self.entrada_n.insert(0, "6")
        self.entrada_n.pack(fill="x", pady=(4, 12))

        tk.Label(
            panel, text="Demostraciones por Inducción:",
            font=("Arial", 11, "bold"), bg="#e2e8f0"
        ).pack(anchor="w", pady=(0, 6))

        opciones = [
            ("1. Suma de los primeros naturales", self.suma_naturales),
            ("2. Divisibilidad: 4^n - 1 entre 3", self.divisibilidad_tres),
            ("3. Desigualdad: 4n < n² - 7 (n ≥ 6)", self.desigualdad),
            ("4. Divisibilidad: 6^(2n) - 1 entre 35", self.divisibilidad_35),
        ]
        for texto, cmd in opciones:
            tk.Button(
                panel, text=texto, command=cmd, bg="#1d4ed8", fg="white",
                font=("Arial", 10, "bold"), pady=6, anchor="w", padx=8
            ).pack(fill="x", pady=3)

        tk.Label(
            panel, text="5. Comprobación de Propiedades:",
            font=("Arial", 11, "bold"), bg="#e2e8f0"
        ).pack(anchor="w", pady=(12, 4))

        self.prop_var = tk.StringVar(value="1")
        props = [
            ("5.1  n² + n es un número par", "1"),
            ("5.2  2^n > n para todo n ≥ 1", "2"),
            ("5.3  n(n + 1) es un número par", "3"),
        ]
        for txt, val in props:
            tk.Radiobutton(
                panel, text=txt, variable=self.prop_var, value=val,
                bg="#e2e8f0", font=("Arial", 10)
            ).pack(anchor="w")

        tk.Button(
            panel, text="Evaluar Propiedad Seleccionada",
            command=self.comprobar_propiedades, bg="#0f766e", fg="white",
            font=("Arial", 10, "bold"), pady=6
        ).pack(fill="x", pady=(8, 4))

        zona = tk.Frame(cuerpo, bg="#f8fafc")
        zona.pack(side="right", fill="both", expand=True, padx=(16, 0))

        tk.Label(
            zona, text="Demostración Formal (Caso Base, Hipótesis, Paso Inductivo y Verificación):",
            font=("Arial", 12, "bold"), bg="#f8fafc"
        ).pack(anchor="w", pady=(0, 6))

        self.salida = tk.Text(
            zona, font=("Consolas", 11), bg="#0f172a", fg="#f8fafc",
            padx=14, pady=14, wrap="word", state="disabled"
        )
        self.salida.pack(fill="both", expand=True)

        self.suma_naturales()

    def _mostrar(self, texto: str) -> None:
        self.salida.config(state="normal")
        self.salida.delete("1.0", "end")
        self.salida.insert("end", texto)
        self.salida.config(state="disabled")

    def _obtener_n(self, minimo: int = 1) -> Optional[int]:
        try:
            n = int(self.entrada_n.get().strip())
            if n < minimo:
                messagebox.showwarning(
                    "Dominio Inválido",
                    f"El valor de n debe ser un número entero mayor o igual a {minimo}."
                )
                return None
            return n
        except ValueError:
            messagebox.showerror("Error", "Ingresa un número entero válido para n.")
            return None

    def suma_naturales(self) -> None:
        n = self._obtener_n(1)
        if n is None:
            return
        suma_real = sum(range(1, n + 1))
        formula = n * (n + 1) // 2
        texto = (
            "====================================================================\n"
            " TEOREMA 1: SUMA DE LOS PRIMEROS NÚMEROS NATURALES\n"
            " Proposición P(n): 1 + 2 + 3 + ... + n = n(n + 1) / 2   ∀ n ≥ 1\n"
            "====================================================================\n\n"
            "1. PASO BASE (n = 1):\n"
            "   • Lado izquierdo : 1\n"
            "   • Lado derecho   : 1(1 + 1) / 2 = 2 / 2 = 1\n"
            "   • Como 1 = 1, P(1) es verdadera.\n\n"
            "2. HIPÓTESIS DE INDUCCIÓN (n = k):\n"
            "   • Se asume que P(k) se cumple para algún k ∈ ℕ:\n"
            "     1 + 2 + ... + k = k(k + 1) / 2\n\n"
            "3. PASO INDUCTIVO (Demostrar para n = k + 1):\n"
            "   • Sumando (k + 1) a ambos miembros de la Hipótesis:\n"
            "     [1 + 2 + ... + k] + (k + 1) = k(k + 1)/2 + (k + 1)\n"
            "                                 = [k(k + 1) + 2(k + 1)] / 2\n"
            "                                 = (k + 1)(k + 2) / 2\n"
            "   • Queda demostrada P(k + 1). ∎\n\n"
            f"4. COMPROBACIÓN NUMÉRICA PARA n = {n}:\n"
            f"   • Suma iterativa real : {suma_real}\n"
            f"   • Fórmula cerrada     : {n}({n} + 1) / 2 = {formula}\n"
            f"   • VEREDICTO           : {'[✓] PROPIEDAD VERIFICADA' if suma_real == formula else '[✗] FALLO'}"
        )
        self._mostrar(texto)

    def divisibilidad_tres(self) -> None:
        n = self._obtener_n(1)
        if n is None:
            return
        resultado = (4 ** n) - 1
        residuo = resultado % 3
        q = resultado // 3
        texto = (
            "====================================================================\n"
            " TEOREMA 2: DIVISIBILIDAD DE 4^n - 1 ENTRE 3\n"
            " Proposición P(n): 3 divide a (4^n - 1)   ∀ n ≥ 1\n"
            "====================================================================\n\n"
            "1. PASO BASE (n = 1):\n"
            "   • 4^1 - 1 = 3 = 3(1), el cual es divisible entre 3.\n\n"
            "2. HIPÓTESIS DE INDUCCIÓN (n = k):\n"
            "   • Se supone que 4^k - 1 = 3m para algún entero m ∈ ℤ.\n\n"
            "3. PASO INDUCTIVO (n = k + 1):\n"
            "   • 4^(k+1) - 1 = 4 · 4^k - 1\n"
            "                 = (3 + 1)4^k - 1\n"
            "                 = 3·4^k + (4^k - 1)\n"
            "                 = 3·4^k + 3m = 3(4^k + m)\n"
            "   • Al ser múltiplo entero de 3, P(k + 1) es verdadera. ∎\n\n"
            f"4. COMPROBACIÓN NUMÉRICA PARA n = {n}:\n"
            f"   • Valor 4^{n} - 1     : {resultado}\n"
            f"   • Descomposición      : 3 × {q} + {residuo}\n"
            f"   • Residuo (mod 3)     : {residuo}\n"
            f"   • VEREDICTO           : {'[✓] ES DIVISIBLE ENTRE 3' if residuo == 0 else '[✗] NO DIVISIBLE'}"
        )
        self._mostrar(texto)

    def desigualdad(self) -> None:
        n = self._obtener_n(6)
        if n is None:
            return
        izq = 4 * n
        der = (n ** 2) - 7
        texto = (
            "====================================================================\n"
            " TEOREMA 3: DESIGUALDAD CUADRÁTICA\n"
            " Proposición P(n): 4n < n² - 7   ∀ n ≥ 6\n"
            "====================================================================\n\n"
            "1. PASO BASE (n = 6):\n"
            "   • Lado izquierdo : 4(6) = 24\n"
            "   • Lado derecho   : 6² - 7 = 36 - 7 = 29\n"
            "   • Como 24 < 29, el caso base n = 6 es verdadero.\n\n"
            "2. HIPÓTESIS DE INDUCCIÓN (n = k, con k ≥ 6):\n"
            "   • Se asume que 4k < k² - 7.\n\n"
            "3. PASO INDUCTIVO (n = k + 1):\n"
            "   • Partimos de: 4(k + 1) = 4k + 4\n"
            "   • Por hipótesis inductiva: 4k + 4 < (k² - 7) + 4\n"
            "   • Como k ≥ 6, se cumple que 4 < 2k + 1, por tanto:\n"
            "     (k² - 7) + 4 < (k² - 7) + (2k + 1) = (k + 1)² - 7\n"
            "   • Por transitividad: 4(k + 1) < (k + 1)² - 7. ∎\n\n"
            f"4. COMPROBACIÓN NUMÉRICA PARA n = {n}:\n"
            f"   • Lado izquierdo (4n)     : {izq}\n"
            f"   • Lado derecho (n² - 7)   : {der}\n"
            f"   • Comparación             : {izq} < {der}\n"
            f"   • VEREDICTO               : {'[✓] DESIGUALDAD VERDADERA' if izq < der else '[✗] FALSA'}"
        )
        self._mostrar(texto)

    def divisibilidad_35(self) -> None:
        n = self._obtener_n(1)
        if n is None:
            return
        resultado = (6 ** (2 * n)) - 1
        residuo = resultado % 35
        texto = (
            "====================================================================\n"
            " TEOREMA 4: DIVISIBILIDAD DE 6^(2n) - 1 ENTRE 35\n"
            " Proposición P(n): 35 divide a (6^(2n) - 1)   ∀ n ≥ 1\n"
            "====================================================================\n\n"
            "1. PASO BASE (n = 1):\n"
            "   • 6^(2·1) - 1 = 36 - 1 = 35 = 35(1). Es divisible entre 35.\n\n"
            "2. HIPÓTESIS DE INDUCCIÓN (n = k):\n"
            "   • Se asume que 6^(2k) - 1 = 35m para algún m ∈ ℤ.\n\n"
            "3. PASO INDUCTIVO (n = k + 1):\n"
            "   • 6^(2(k+1)) - 1 = 6^(2k + 2) - 1\n"
            "                    = 36 · 6^(2k) - 1\n"
            "                    = 36(6^(2k) - 1) + 35\n"
            "                    = 36(35m) + 35 = 35(36m + 1)\n"
            "   • Es múltiplo entero de 35. Queda demostrado. ∎\n\n"
            f"4. COMPROBACIÓN NUMÉRICA PARA n = {n}:\n"
            f"   • Valor 6^(2·{n}) - 1 : {resultado}\n"
            f"   • Residuo (mod 35)    : {residuo}\n"
            f"   • VEREDICTO           : {'[✓] ES DIVISIBLE ENTRE 35' if residuo == 0 else '[✗] NO DIVISIBLE'}"
        )
        self._mostrar(texto)

    def comprobar_propiedades(self) -> None:
        n = self._obtener_n(1)
        if n is None:
            return
        op = self.prop_var.get()
        if op == "1":
            res = n ** 2 + n
            cumple = (res % 2 == 0)
            detalle = (
                f"PROPIEDAD 5.1: P(n): n² + n es par\n\n"
                f"• Factorización algebraica : n² + n = n(n + 1)\n"
                f"• Argumento de paridad     : Producto de dos enteros consecutivos.\n"
                f"• Evaluación en n = {n}     : {n}² + {n} = {res}\n"
                f"• Residuo mod 2            : {res % 2}\n"
                f"• Conclusión               : {'[✓] SE CUMPLE (Es par)' if cumple else '[✗] NO SE CUMPLE'}"
            )
        elif op == "2":
            res = 2 ** n
            cumple = (res > n)
            detalle = (
                f"PROPIEDAD 5.2: P(n): 2^n > n\n\n"
                f"• Caso base (n=1)          : 2¹ = 2 > 1\n"
                f"• Paso inductivo           : 2^(k+1) = 2·2^k > 2k = k + k ≥ k + 1\n"
                f"• Evaluación en n = {n}     : 2^{n} = {res}  vs  n = {n}\n"
                f"• Conclusión               : {'[✓] SE CUMPLE (2^n > n)' if cumple else '[✗] NO SE CUMPLE'}"
            )
        else:
            res = n * (n + 1)
            cumple = (res % 2 == 0)
            detalle = (
                f"PROPIEDAD 5.3: P(n): n(n + 1) es par\n\n"
                f"• Demostración directa     : Entre n y (n + 1), exactamente uno es múltiplo de 2.\n"
                f"• Evaluación en n = {n}     : {n}({n + 1}) = {res}\n"
                f"• Residuo mod 2            : {res % 2}\n"
                f"• Conclusión               : {'[✓] SE CUMPLE (Es par)' if cumple else '[✗] NO SE CUMPLE'}"
            )
        self._mostrar(detalle)


# ==============================================================================
# MÓDULO 2: IMPORT TKINTER (COMBINATORIA Y CONTEO)
# ==============================================================================

class Modulo2CombinatoriaTkinter(tk.Frame):
    def __init__(self, parent: tk.Widget) -> None:
        super().__init__(parent, bg="#f8fafc")
        self._construir_ui()

    def _construir_ui(self) -> None:
        header = tk.Label(
            self, text="MÓDULO 2: CALCULADORA DE CONTEO Y COMBINATORIA (TKINTER)",
            font=("Arial", 16, "bold"), bg="#1e3a8a", fg="white", pady=12
        )
        header.pack(fill="x")

        cuerpo = tk.Frame(self, bg="#f8fafc", padx=20, pady=16)
        cuerpo.pack(fill="both", expand=True)

        self.notebook = ttk.Notebook(cuerpo)
        self.notebook.pack(side="left", fill="both", expand=True)

        self.tab_principio = ttk.Frame(self.notebook)
        self.tab_permutacion = ttk.Frame(self.notebook)
        self.tab_combinacion = ttk.Frame(self.notebook)

        self.notebook.add(self.tab_principio, text="1. Principio Multiplicativo")
        self.notebook.add(self.tab_permutacion, text="2. Permutaciones P(n, r)")
        self.notebook.add(self.tab_combinacion, text="3. Combinaciones C(n, r)")

        self.bitacora = tk.Text(
            cuerpo, width=48, font=("Consolas", 11), bg="#0f172a", fg="#f8fafc",
            padx=12, pady=12, wrap="word", state="disabled"
        )
        self.bitacora.pack(side="right", fill="y", padx=(16, 0))

        self._setup_tab_principio()
        self._setup_tab_nr(
            self.tab_permutacion,
            "Permutaciones Ordinarias — P(n, r) = n! / (n - r)!\n(El orden de los elementos SÍ importa)",
            self.calcular_permutacion
        )
        self._setup_tab_nr(
            self.tab_combinacion,
            "Combinaciones — C(n, r) = n! / [r!(n - r)!]\n(El orden de los elementos NO importa)",
            self.calcular_combinacion
        )
        self._escribir_bitacora(
            "MÓDULO DE COMBINATORIA\n\n"
            "Seleccioná una pestaña a la izquierda para calcular:\n"
            "• Principio Fundamental del Conteo\n"
            "• Permutaciones sin repetición P(n, r)\n"
            "• Combinaciones sin repetición C(n, r)"
        )

    def _escribir_bitacora(self, texto: str) -> None:
        self.bitacora.config(state="normal")
        self.bitacora.delete("1.0", "end")
        self.bitacora.insert("end", texto)
        self.bitacora.config(state="disabled")

    def _setup_tab_principio(self) -> None:
        ttk.Label(
            self.tab_principio,
            text="Principio Multiplicativo del Conteo\n"
                 "Ingresa las opciones de cada etapa separadas por comas (ej. 3, 4, 2):",
            justify="center", font=("Helvetica", 12, "bold")
        ).pack(pady=24)

        self.entry_eventos = ttk.Entry(self.tab_principio, width=32, font=("Helvetica", 13))
        self.entry_eventos.insert(0, "3, 4, 2")
        self.entry_eventos.pack(pady=10)

        tk.Button(
            self.tab_principio, text="Calcular Producto Cartesiano",
            command=self.calcular_principio, bg="#2563eb", fg="white",
            font=("Helvetica", 11, "bold"), padx=14, pady=6
        ).pack(pady=15)

        self.lbl_resultado_principio = ttk.Label(
            self.tab_principio, text="Resultado: -",
            font=("Helvetica", 15, "bold"), foreground="#2563eb"
        )
        self.lbl_resultado_principio.pack(pady=10)

    def _setup_tab_nr(self, tab: ttk.Frame, titulo: str, comando_calcular) -> None:
        ttk.Label(tab, text=titulo, justify="center", font=("Helvetica", 12, "bold")).pack(pady=20)

        frame_inputs = ttk.Frame(tab)
        frame_inputs.pack(pady=10)

        ttk.Label(frame_inputs, text="Total de elementos (n):").grid(row=0, column=0, padx=8, pady=8, sticky="e")
        entry_n = ttk.Entry(frame_inputs, width=12, font=("Helvetica", 12))
        entry_n.insert(0, "10")
        entry_n.grid(row=0, column=1, padx=8, pady=8)

        ttk.Label(frame_inputs, text="Elementos a elegir (r):").grid(row=1, column=0, padx=8, pady=8, sticky="e")
        entry_r = ttk.Entry(frame_inputs, width=12, font=("Helvetica", 12))
        entry_r.insert(0, "3")
        entry_r.grid(row=1, column=1, padx=8, pady=8)

        lbl_res = ttk.Label(
            tab, text="Resultado: -", font=("Helvetica", 15, "bold"), foreground="#059669"
        )
        tk.Button(
            tab, text="Calcular", bg="#059669", fg="white",
            font=("Helvetica", 11, "bold"), padx=16, pady=6,
            command=lambda: comando_calcular(entry_n, entry_r, lbl_res)
        ).pack(pady=15)
        lbl_res.pack(pady=10)

    def calcular_principio(self) -> None:
        try:
            texto = self.entry_eventos.get()
            numeros = [int(x.strip()) for x in texto.split(",") if x.strip()]
            if not numeros or any(n <= 0 for n in numeros):
                raise ValueError
            total = math.prod(numeros)
            self.lbl_resultado_principio.config(text=f"Resultado: {total:,}")
            expresion = " × ".join(str(n) for n in numeros)
            self._escribir_bitacora(
                "PRINCIPIO MULTIPLICATIVO\n"
                "========================================\n"
                f"• Etapas (k)       : {len(numeros)} eventos independientes\n"
                f"• Opciones         : {numeros}\n"
                f"• Desarrollo       : {expresion}\n"
                f"• Total de formas  : {total:,}"
            )
        except ValueError:
            messagebox.showerror("Error", "Ingresa únicamente enteros positivos separados por comas.")

    def calcular_permutacion(self, entry_n: ttk.Entry, entry_r: ttk.Entry, label_res: ttk.Label) -> None:
        try:
            n = int(entry_n.get())
            r = int(entry_r.get())
            if r > n or n < 0 or r < 0:
                raise ValueError
            resultado = math.perm(n, r)
            label_res.config(text=f"P({n}, {r}) = {resultado:,}")
            self._escribir_bitacora(
                "PERMUTACIONES SIN REPETICIÓN\n"
                "========================================\n"
                f"• Fórmula          : P(n, r) = n! / (n - r)!\n"
                f"• Sustitución      : {n}! / ({n} - {r})! = {n}! / {n - r}!\n"
                f"• Resultado exacto : P({n}, {r}) = {resultado:,}"
            )
        except ValueError:
            messagebox.showerror("Error", "Verifica que n y r sean enteros no negativos con 0 <= r <= n.")

    def calcular_combinacion(self, entry_n: ttk.Entry, entry_r: ttk.Entry, label_res: ttk.Label) -> None:
        try:
            n = int(entry_n.get())
            r = int(entry_r.get())
            if r > n or n < 0 or r < 0:
                raise ValueError
            resultado = math.comb(n, r)
            label_res.config(text=f"C({n}, {r}) = {resultado:,}")
            self._escribir_bitacora(
                "COMBINACIONES SIN REPETICIÓN\n"
                "========================================\n"
                f"• Fórmula          : C(n, r) = n! / [r!(n - r)!]\n"
                f"• Sustitución      : {n}! / [{r}! · {n - r}!]\n"
                f"• Resultado exacto : C({n}, {r}) = {resultado:,}"
            )
        except ValueError:
            messagebox.showerror("Error", "Verifica que n y r sean enteros no negativos con 0 <= r <= n.")


# ==============================================================================
# MÓDULO 3: SISTEMA ARITMÉTICA
# ==============================================================================

class Modulo3SistemaAritmetica(tk.Frame):
    def __init__(self, parent: tk.Widget) -> None:
        super().__init__(parent, bg="#f8fafc")
        self._construir_ui()

    def _construir_ui(self) -> None:
        titulo = tk.Label(
            self, text="MÓDULO 3: SISTEMA INTERACTIVO DE ARITMÉTICA ENTERA",
            font=("Arial", 16, "bold"), bg="#17324d", fg="white", pady=12
        )
        titulo.pack(fill="x")

        principal = tk.Frame(self, bg="#f8fafc", padx=18, pady=14)
        principal.pack(fill="both", expand=True)

        panel = tk.Frame(principal, bg="#edf2f7", padx=14, pady=14)
        panel.pack(side="left", fill="y")

        tk.Label(panel, text="Número 1 (a):", font=("Arial", 11, "bold"), bg="#edf2f7").pack(anchor="w")
        self.entrada_a = tk.Entry(panel, font=("Arial", 12), width=23)
        self.entrada_a.insert(0, "252")
        self.entrada_a.pack(pady=(4, 12))

        tk.Label(panel, text="Número 2 (b):", font=("Arial", 11, "bold"), bg="#edf2f7").pack(anchor="w")
        self.entrada_b = tk.Entry(panel, font=("Arial", 12), width=23)
        self.entrada_b.insert(0, "198")
        self.entrada_b.pack(pady=(4, 14))

        tk.Label(panel, text="Operaciones", font=("Arial", 13, "bold"), bg="#edf2f7").pack(anchor="w", pady=(0, 7))

        botones = [
            ("Factorización prima (Teorema Fundamental)", self.factorizacion),
            ("Máximo Común Divisor (MCD + Bézout)", self.mcd),
            ("Algoritmo de la División (a = bq + r)", self.division),
            ("Algoritmo de Euclides Paso a Paso", self.euclides),
        ]
        for texto, comando in botones:
            tk.Button(
                panel, text=texto, command=comando, bg="#2563eb", fg="white",
                activebackground="#1d4ed8", font=("Arial", 10, "bold"),
                wraplength=210, pady=7
            ).pack(fill="x", pady=4)

        tk.Button(
            panel, text="Limpiar", command=self.limpiar,
            bg="#b91c1c", fg="white", font=("Arial", 10, "bold"), pady=7
        ).pack(fill="x", pady=(14, 4))

        zona = tk.Frame(principal, bg="#f8fafc")
        zona.pack(side="right", fill="both", expand=True, padx=(18, 0))

        tk.Label(
            zona, text="Procedimiento algebraico y resultado",
            font=("Arial", 13, "bold"), bg="#f8fafc"
        ).pack(anchor="w", pady=(0, 8))

        self.resultado = tk.Text(
            zona, font=("Consolas", 11), bg="#0f172a", fg="#f8fafc",
            wrap="word", padx=12, pady=12, state="disabled"
        )
        self.resultado.pack(fill="both", expand=True)

        self.mostrar(
            "¡Bienvenido al Módulo de Teoría de Números!\n\n"
            "• Factorización prima: Descompone el Número 1 en potencias primas canónicas.\n"
            "• MCD y Bézout: Calcula MCD(a, b), MCM(a, b) y coeficientes de Bézout.\n"
            "• Algoritmo de la División: Calcula q y r tales que a = b·q + r con 0 ≤ r < |b|.\n"
            "• Algoritmo de Euclides: Muestra las divisiones sucesivas."
        )

    def mostrar(self, texto: str) -> None:
        self.resultado.config(state="normal")
        self.resultado.delete("1.0", "end")
        self.resultado.insert("end", texto)
        self.resultado.config(state="disabled")

    def obtener_a(self) -> Optional[int]:
        try:
            return int(self.entrada_a.get().strip())
        except ValueError:
            messagebox.showwarning("Dato incorrecto", "Ingresá un número entero en Número 1.")
            return None

    def obtener_dos(self) -> Tuple[Optional[int], Optional[int]]:
        a = self.obtener_a()
        if a is None:
            return None, None
        try:
            b = int(self.entrada_b.get().strip())
            return a, b
        except ValueError:
            messagebox.showwarning("Dato incorrecto", "Ingresá un número entero en Número 2.")
            return None, None

    def factorizacion(self) -> None:
        n = self.obtener_a()
        if n is None:
            return
        if n < 2:
            messagebox.showwarning("Número no válido", "La factorización prima requiere un entero mayor que 1.")
            return
        original = n
        factores: List[int] = []
        divisor = 2
        while divisor * divisor <= n:
            while n % divisor == 0:
                factores.append(divisor)
                n //= divisor
            divisor += 1
        if n > 1:
            factores.append(n)

        conteo = Counter(factores)
        expresion = " × ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in conteo.items())
        pasos = [f"TEOREMA FUNDAMENTAL DE LA ARITMÉTICA — FACTORIZACIÓN DE {original}", "=" * 64, ""]
        restante = original
        for p in factores:
            pasos.append(f"  {restante:>10} ÷ {p:<6} = {restante // p}")
            restante //= p
        cantidad_divisores = math.prod(e + 1 for e in conteo.values())
        pasos += [
            "",
            f"• Descomposición canónica : {original} = {expresion}",
            f"• Total de divisores τ(n) : {cantidad_divisores}"
        ]
        self.mostrar("\n".join(pasos))

    def _euclides_extendido(self, a: int, b: int) -> Tuple[int, int, int]:
        if b == 0:
            return (1, 0, a) if a >= 0 else (-1, 0, -a)
        x1, y1, d = self._euclides_extendido(b, a % b)
        return y1, x1 - (a // b) * y1, d

    def mcd(self) -> None:
        a, b = self.obtener_dos()
        if a is None or b is None:
            return
        x, y = abs(a), abs(b)
        if x == 0 and y == 0:
            messagebox.showwarning("Datos no válidos", "El MCD de 0 y 0 no está definido.")
            return

        pasos = [f"MÁXIMO COMÚN DIVISOR E IDENTIDAD DE BÉZOUT PARA ({a}, {b})", "=" * 64, ""]
        while y != 0:
            cociente, residuo = divmod(x, y)
            pasos.append(f"  {x} = {y} × {cociente} + {residuo}")
            x, y = y, residuo

        s, t, d = self._euclides_extendido(a, b)
        mcm = abs(a * b) // d if d != 0 else 0
        pasos += [
            "",
            f"• Resultado MCD({a}, {b})   = {x}",
            f"• Resultado MCM({a}, {b})   = {mcm}",
            f"• Identidad de Bézout       : ({a})({s}) + ({b})({t}) = {d}"
        ]
        self.mostrar("\n".join(pasos))

    def division(self) -> None:
        a, b = self.obtener_dos()
        if a is None or b is None:
            return
        if b == 0:
            messagebox.showwarning("División no válida", "No se puede dividir entre cero.")
            return
        if a < 0 or b < 0:
            messagebox.showwarning("Dato no válido", "Ingresá enteros no negativos y un divisor mayor que cero.")
            return

        q, r = divmod(a, b)
        self.mostrar(
            "ALGORITMO DE LA DIVISIÓN DE EUCLIDES\n"
            "================================================================\n\n"
            f"• Dividendo (a) : {a}\n"
            f"• Divisor   (b) : {b}\n"
            f"• Cociente  (q) : {q}\n"
            f"• Residuo   (r) : {r}\n\n"
            f"Comprobación formal (a = b·q + r con 0 ≤ r < b):\n"
            f"  {a} = ({b} × {q}) + {r}\n"
            f"  {a} = {b * q} + {r}\n"
            f"  Condición de frontera: 0 ≤ {r} < {b}  [✓]"
        )

    def euclides(self) -> None:
        a, b = self.obtener_dos()
        if a is None or b is None:
            return
        x, y = abs(a), abs(b)
        if x == 0 and y == 0:
            messagebox.showwarning("Datos no válidos", "No se puede calcular el MCD de 0 y 0.")
            return
        pasos = [f"ALGORITMO DE EUCLIDES PARA {a} Y {b}", "=" * 64, ""]
        iteracion = 1
        while y != 0:
            q, r = divmod(x, y)
            pasos.append(f"  Paso {iteracion}: {x} = {y} × {q} + {r}")
            x, y = y, r
            iteracion += 1
        pasos += [
            "",
            f"Como el último residuo no nulo es {x},",
            f"se concluye que MCD({a}, {b}) = {x}."
        ]
        self.mostrar("\n".join(pasos))

    def limpiar(self) -> None:
        self.entrada_a.delete(0, "end")
        self.entrada_b.delete(0, "end")
        self.mostrar("Ingresá los números y seleccioná una operación.")


# ==============================================================================
# MÓDULO 4: SISTEMA DE GRAFOS (VISUALIZACIÓN Y MATRICES)
# ==============================================================================

class Modulo4SistemaGrafos(tk.Frame):
    def __init__(self, parent: tk.Widget) -> None:
        super().__init__(parent, bg="#f8fafc")
        self.grafo: Dict[str, Set[str]] = {
            "A": {"B", "D"},
            "B": {"A", "C", "D"},
            "C": {"B", "D"},
            "D": {"A", "B", "C"},
        }
        self._construir_ui()

    def _construir_ui(self) -> None:
        titulo = tk.Label(
            self, text="MÓDULO 4: SISTEMA INTERACTIVO DE GRAFOS (REPRESENTACIONES)",
            font=("Arial", 16, "bold"), bg="#17324d", fg="white", pady=12
        )
        titulo.pack(fill="x")

        principal = tk.Frame(self, bg="#f8fafc", padx=12, pady=10)
        principal.pack(fill="both", expand=True)

        panel = tk.Frame(principal, width=270, bg="#edf2f7", padx=12, pady=12)
        panel.pack(side="left", fill="y")
        panel.pack_propagate(False)

        tk.Label(panel, text="Agregar vértice", font=("Arial", 11, "bold"), bg="#edf2f7").pack(anchor="w")
        self.entrada_vertice = tk.Entry(panel, font=("Arial", 11))
        self.entrada_vertice.pack(fill="x", pady=4)
        tk.Button(
            panel, text="Agregar vértice", command=self.agregar_vertice,
            bg="#2563eb", fg="white", font=("Arial", 10, "bold")
        ).pack(fill="x", pady=(0, 12))

        tk.Label(panel, text="Conectar vértices (origen / destino)", font=("Arial", 11, "bold"), bg="#edf2f7").pack(anchor="w")
        self.entrada_origen = tk.Entry(panel, font=("Arial", 11))
        self.entrada_origen.pack(fill="x", pady=3)
        self.entrada_destino = tk.Entry(panel, font=("Arial", 11))
        self.entrada_destino.pack(fill="x", pady=3)
        tk.Button(
            panel, text="Agregar arista", command=self.agregar_arista,
            bg="#0f766e", fg="white", font=("Arial", 10, "bold")
        ).pack(fill="x", pady=(4, 12))

        tk.Label(panel, text="Información estructural", font=("Arial", 11, "bold"), bg="#edf2f7").pack(anchor="w", pady=(0, 4))
        tk.Button(panel, text="Mostrar lista de adyacencia", command=self.mostrar_lista).pack(fill="x", pady=3)
        tk.Button(panel, text="Mostrar matriz de adyacencia", command=self.mostrar_matriz).pack(fill="x", pady=3)
        tk.Button(panel, text="Mostrar grados y lema del apretón", command=self.mostrar_grados).pack(fill="x", pady=3)
        tk.Button(
            panel, text="Limpiar grafo", command=self.limpiar_grafo,
            bg="#b91c1c", fg="white", font=("Arial", 10, "bold")
        ).pack(fill="x", pady=(12, 3))

        zona = tk.Frame(principal, bg="#f8fafc")
        zona.pack(side="right", fill="both", expand=True, padx=(12, 0))

        tk.Label(zona, text="Representación visual", font=("Arial", 13, "bold"), bg="#f8fafc").pack()
        self.lienzo = tk.Canvas(zona, bg="white", highlightthickness=1, highlightbackground="#cbd5e1")
        self.lienzo.pack(fill="both", expand=True, pady=6)
        self.lienzo.bind("<Configure>", lambda e: self.dibujar_grafo())

        tk.Label(zona, text="Resultados", font=("Arial", 11, "bold"), bg="#f8fafc").pack(anchor="w")
        self.resultado = tk.Text(
            zona, height=8, font=("Consolas", 10), bg="#0f172a", fg="#f8fafc",
            wrap="word", state="disabled", padx=10, pady=8
        )
        self.resultado.pack(fill="x")

        self.mostrar_lista()

    def actualizar_resultado(self, texto: str) -> None:
        self.resultado.config(state="normal")
        self.resultado.delete("1.0", "end")
        self.resultado.insert("end", texto)
        self.resultado.config(state="disabled")

    def agregar_vertice(self) -> None:
        vertice = self.entrada_vertice.get().strip()
        if not vertice:
            messagebox.showwarning("Dato faltante", "Escribí el nombre del vértice.")
        elif vertice in self.grafo:
            messagebox.showinfo("Aviso", "Ese vértice ya existe.")
        else:
            self.grafo[vertice] = set()
            self.entrada_vertice.delete(0, "end")
            self.dibujar_grafo()
            self.actualizar_resultado(f"Vértice agregado: {vertice}")

    def agregar_arista(self) -> None:
        origen = self.entrada_origen.get().strip()
        destino = self.entrada_destino.get().strip()
        if origen not in self.grafo or destino not in self.grafo:
            messagebox.showwarning("Vértices no encontrados", "Primero agregá ambos vértices al grafo.")
        elif origen == destino:
            messagebox.showwarning("Conexión no válida", "Grafo simple: no se permiten lazos.")
        elif destino in self.grafo[origen]:
            messagebox.showinfo("Aviso", "Esa arista ya existe.")
        else:
            self.grafo[origen].add(destino)
            self.grafo[destino].add(origen)
            self.entrada_origen.delete(0, "end")
            self.entrada_destino.delete(0, "end")
            self.dibujar_grafo()
            self.actualizar_resultado(f"Arista agregada: {origen} — {destino}")

    def posiciones(self) -> Dict[str, Tuple[float, float]]:
        vertices = list(self.grafo.keys())
        cantidad = len(vertices)
        ancho = max(self.lienzo.winfo_width(), 400)
        alto = max(self.lienzo.winfo_height(), 260)
        cx, cy = ancho / 2, alto / 2
        radio = max(60, min(ancho, alto) * 0.35)
        pos: Dict[str, Tuple[float, float]] = {}
        for i, v in enumerate(vertices):
            ang = -math.pi / 2 + (2 * math.pi * i / cantidad)
            pos[v] = (cx + radio * math.cos(ang), cy + radio * math.sin(ang))
        return pos

    def dibujar_grafo(self) -> None:
        self.lienzo.delete("all")
        if not self.grafo:
            self.lienzo.create_text(
                max(self.lienzo.winfo_width(), 400) / 2,
                max(self.lienzo.winfo_height(), 260) / 2,
                text="Tu grafo aparecerá aquí", fill="#64748b", font=("Arial", 15)
            )
            return
        pos = self.posiciones()
        claves = list(self.grafo.keys())
        for origen in claves:
            for destino in self.grafo[origen]:
                if claves.index(origen) < claves.index(destino):
                    x1, y1 = pos[origen]
                    x2, y2 = pos[destino]
                    self.lienzo.create_line(x1, y1, x2, y2, fill="#64748b", width=3)
        for v, (x, y) in pos.items():
            self.lienzo.create_oval(x - 22, y - 22, x + 22, y + 22, fill="#2563eb", outline="#17324d", width=2)
            self.lienzo.create_text(x, y, text=v, fill="white", font=("Arial", 11, "bold"))

    def mostrar_lista(self) -> None:
        if not self.grafo:
            self.actualizar_resultado("El grafo está vacío.")
            return
        lineas = ["LISTA DE ADYACENCIA"]
        for v, vecinos in self.grafo.items():
            lineas.append(f"  {v} -> {', '.join(sorted(vecinos)) if vecinos else 'Sin conexiones'}")
        self.actualizar_resultado("\n".join(lineas))

    def mostrar_matriz(self) -> None:
        vertices = list(self.grafo.keys())
        if not vertices:
            self.actualizar_resultado("El grafo está vacío.")
            return
        ancho = max(4, max(len(v) for v in vertices) + 1)
        lineas = ["MATRIZ DE ADYACENCIA"]
        lineas.append("".ljust(ancho) + "".join(v.center(ancho) for v in vertices))
        for o in vertices:
            fila = o.ljust(ancho) + "".join(
                ("1" if d in self.grafo[o] else "0").center(ancho) for d in vertices
            )
            lineas.append(fila)
        self.actualizar_resultado("\n".join(lineas))

    def mostrar_grados(self) -> None:
        if not self.grafo:
            self.actualizar_resultado("El grafo está vacío.")
            return
        lineas = ["GRADO DE CADA VÉRTICE Y LEMA DEL APRETÓN DE MANOS"]
        suma_grados = 0
        for v, vecinos in self.grafo.items():
            g = len(vecinos)
            suma_grados += g
            lineas.append(f"  deg({v}) = {g}")
        aristas = suma_grados // 2
        lineas.append(f"\n• Total de vértices |V| = {len(self.grafo)}")
        lineas.append(f"• Total de aristas  |E| = {aristas}")
        lineas.append(f"• Verificación ∑ deg(v) = {suma_grados} = 2|E| = {2 * aristas}  [✓]")
        self.actualizar_resultado("\n".join(lineas))

    def limpiar_grafo(self) -> None:
        if messagebox.askyesno("Confirmar", "¿Querés borrar todos los vértices y conexiones?"):
            self.grafo.clear()
            self.dibujar_grafo()
            self.actualizar_resultado("El grafo se limpió correctamente.")


# ==============================================================================
# MÓDULO 5: GRAFOS (RUTAS, CIRCUITOS, EULER, HAMILTON E ISOMORFISMO)
# ==============================================================================

class Modulo5TeoriaGrafos(tk.Frame):
    """
    Reimplementación universitaria autocontenida de grafos.py sin depender de
    librerías externas (NetworkX), garantizando portabilidad 100%.
    """

    def __init__(self, parent: tk.Widget) -> None:
        super().__init__(parent, bg="#f8fafc")
        self.grafo: Dict[str, Set[str]] = {}
        self._construir_ui()
        self.cargar_grafo_actual()

    def _construir_ui(self) -> None:
        header = tk.Label(
            self, text="MÓDULO 5: TEORÍA DE GRAFOS — EULER, HAMILTON, RUTAS E ISOMORFISMO",
            font=("Arial", 16, "bold"), bg="#0f766e", fg="white", pady=12
        )
        header.pack(fill="x")

        cuerpo = tk.Frame(self, bg="#f8fafc", padx=14, pady=10)
        cuerpo.pack(fill="both", expand=True)

        panel = tk.Frame(cuerpo, width=335, bg="#e2e8f0", padx=12, pady=10)
        panel.pack(side="left", fill="y")
        panel.pack_propagate(False)

        tk.Label(panel, text="1. Definir Grafo Principal G1", font=("Arial", 11, "bold"), bg="#e2e8f0").pack(anchor="w")
        tk.Label(panel, text="Vértices (separados por coma):", font=("Arial", 9), bg="#e2e8f0").pack(anchor="w")
        self.ent_vertices = tk.Entry(panel, font=("Arial", 10))
        self.ent_vertices.insert(0, "A, B, C, D")
        self.ent_vertices.pack(fill="x", pady=2)

        tk.Label(panel, text="Aristas (formato A-B, B-C):", font=("Arial", 9), bg="#e2e8f0").pack(anchor="w")
        self.ent_aristas = tk.Entry(panel, font=("Arial", 10))
        self.ent_aristas.insert(0, "A-B, B-C, C-D, D-A")
        self.ent_aristas.pack(fill="x", pady=2)

        tk.Button(
            panel, text="Cargar / Actualizar Grafo G1", command=self.cargar_grafo_actual,
            bg="#0f766e", fg="white", font=("Arial", 10, "bold")
        ).pack(fill="x", pady=(4, 8))

        tk.Label(panel, text="2. Consultas y Algoritmos", font=("Arial", 11, "bold"), bg="#e2e8f0").pack(anchor="w")

        fr_ruta = tk.Frame(panel, bg="#e2e8f0")
        fr_ruta.pack(fill="x", pady=2)
        tk.Label(fr_ruta, text="Inicio:", bg="#e2e8f0", font=("Arial", 9)).pack(side="left")
        self.ent_ini = tk.Entry(fr_ruta, width=5)
        self.ent_ini.insert(0, "A")
        self.ent_ini.pack(side="left", padx=4)
        tk.Label(fr_ruta, text="Fin:", bg="#e2e8f0", font=("Arial", 9)).pack(side="left")
        self.ent_fin = tk.Entry(fr_ruta, width=5)
        self.ent_fin.insert(0, "C")
        self.ent_fin.pack(side="left", padx=4)
        tk.Button(
            fr_ruta, text="Ruta más corta (BFS)", command=self.buscar_ruta,
            bg="#2563eb", fg="white", font=("Arial", 9, "bold")
        ).pack(side="right")

        botones = [
            ("Información Teórica Completa", self.mostrar_informacion),
            ("Analizar Vértices, Aristas y Conexidad", self.analizar_grafo),
            ("Buscar un Circuito (DFS)", self.buscar_circuito),
            ("Evaluar Circuito de Euler (Hierholzer)", self.evaluar_euler),
            ("Evaluar Camino y Ciclo de Hamilton", self.buscar_hamilton),
        ]
        for txt, cmd in botones:
            tk.Button(
                panel, text=txt, command=cmd, bg="#1e293b", fg="white",
                font=("Arial", 9, "bold"), pady=4
            ).pack(fill="x", pady=2)

        tk.Label(panel, text="3. Comparar Isomorfismo con G2", font=("Arial", 11, "bold"), bg="#e2e8f0").pack(anchor="w", pady=(8, 2))
        tk.Label(panel, text="Vértices G2:", font=("Arial", 9), bg="#e2e8f0").pack(anchor="w")
        self.ent_v2 = tk.Entry(panel, font=("Arial", 10))
        self.ent_v2.insert(0, "1, 2, 3, 4")
        self.ent_v2.pack(fill="x", pady=1)

        tk.Label(panel, text="Aristas G2:", font=("Arial", 9), bg="#e2e8f0").pack(anchor="w")
        self.ent_a2 = tk.Entry(panel, font=("Arial", 10))
        self.ent_a2.insert(0, "1-2, 2-3, 3-4, 4-1")
        self.ent_a2.pack(fill="x", pady=1)

        tk.Button(
            panel, text="Verificar Isomorfismo (G1 ≅ G2)", command=self.comparar_isomorfismo,
            bg="#7c3aed", fg="white", font=("Arial", 10, "bold"), pady=4
        ).pack(fill="x", pady=(4, 2))

        zona = tk.Frame(cuerpo, bg="#f8fafc")
        zona.pack(side="right", fill="both", expand=True, padx=(14, 0))

        tk.Label(zona, text="Consola de Análisis de Grafos:", font=("Arial", 12, "bold"), bg="#f8fafc").pack(anchor="w")
        self.consola = tk.Text(
            zona, font=("Consolas", 11), bg="#0f172a", fg="#f8fafc",
            padx=14, pady=14, wrap="word", state="disabled"
        )
        self.consola.pack(fill="both", expand=True, pady=(6, 0))

    def _escribir(self, texto: str) -> None:
        self.consola.config(state="normal")
        self.consola.delete("1.0", "end")
        self.consola.insert("end", texto)
        self.consola.config(state="disabled")

    def _parsear_grafo(self, txt_v: str, txt_a: str) -> Optional[Dict[str, Set[str]]]:
        vertices = [v.strip() for v in txt_v.split(",") if v.strip()]
        if not vertices:
            messagebox.showwarning("Error", "Debes ingresar al menos un vértice.")
            return None
        if len(vertices) != len(set(vertices)):
            messagebox.showwarning("Error", "No puedes repetir nombres de vértices.")
            return None
        g: Dict[str, Set[str]] = {v: set() for v in vertices}
        if txt_a.strip():
            for item in txt_a.split(","):
                partes = item.strip().split("-")
                if len(partes) != 2:
                    messagebox.showerror("Error", f"Formato inválido en arista '{item}'. Usa A-B.")
                    return None
                u, v = partes[0].strip(), partes[1].strip()
                if u not in g or v not in g:
                    messagebox.showerror("Error", f"La arista '{u}-{v}' usa vértices no declarados.")
                    return None
                if u != v:
                    g[u].add(v)
                    g[v].add(u)
        return g

    def cargar_grafo_actual(self) -> None:
        g = self._parsear_grafo(self.ent_vertices.get(), self.ent_aristas.get())
        if g is not None:
            self.grafo = g
            self.analizar_grafo()

    def mostrar_informacion(self) -> None:
        self._escribir(
            "======================================================================\n"
            " FUNDAMENTOS TEÓRICOS DE LA TEORÍA DE GRAFOS\n"
            "======================================================================\n\n"
            "1. GRAFOS ETIQUETADOS:\n"
            "   Un grafo G = (V, E) cuyos vértices poseen identificadores únicos.\n\n"
            "2. RUTAS Y CAMINOS:\n"
            "   Sucesión alternada de vértices y aristas que permite desplazarse\n"
            "   desde un vértice origen hasta un destino. Un camino simple no repite vértices.\n\n"
            "3. GRAFOS ISOMORFOS (G1 ≅ G2):\n"
            "   Existe una biyección f: V(G1) -> V(G2) tal que (u, v) ∈ E(G1) si y solo si\n"
            "   (f(u), f(v)) ∈ E(G2).\n\n"
            "4. CIRCUITOS Y CICLOS:\n"
            "   Un recorrido cerrado que inicia y finaliza en el mismo vértice.\n\n"
            "5. CIRCUITO DE EULER:\n"
            "   Recorrido cerrado que atraviesa cada arista exactamente una vez.\n"
            "   Teorema de Euler: Un grafo conexo no dirigido posee circuito euleriano\n"
            "   si y solo si TODOS sus vértices tienen grado par.\n\n"
            "6. CAMINOS Y CICLOS DE HAMILTON:\n"
            "   Un camino hamiltoniano visita cada vértice exactamente una vez.\n"
            "   Un ciclo hamiltoniano regresa además al vértice de partida."
        )

    def _es_conexo(self, g: Dict[str, Set[str]]) -> bool:
        if not g:
            return False
        inicio = next(iter(g))
        visitados = {inicio}
        cola = deque([inicio])
        while cola:
            u = cola.popleft()
            for w in g[u]:
                if w not in visitados:
                    visitados.add(w)
                    cola.append(w)
        return len(visitados) == len(g)

    def analizar_grafo(self) -> None:
        if not self.grafo:
            self._escribir("Primero debes cargar un grafo válido.")
            return
        aristas = []
        claves = list(self.grafo.keys())
        for i, u in enumerate(claves):
            for v in sorted(self.grafo[u]):
                if claves.index(u) < claves.index(v):
                    aristas.append(f"{u}-{v}")
        grados = {v: len( self.grafo[v]) for v in claves}
        conexo = self._es_conexo(self.grafo)
        self._escribir(
            "======================================================================\n"
            " ANÁLISIS ESTRUCTURAL DEL GRAFO G1\n"
            "======================================================================\n\n"
            f"• Vértices V(G)         : {claves}\n"
            f"• Aristas  E(G)         : {aristas}\n"
            f"• Orden |V|             : {len(claves)}\n"
            f"• Tamaño |E|            : {len(aristas)}\n"
            f"• Grado de cada vértice : {grados}\n"
            f"• ¿Es conexo?           : {'Sí (1 componente conexa)' if conexo else 'No (Grafo desconectado)'}"
        )

    def buscar_ruta(self) -> None:
        ini = self.ent_ini.get().strip()
        fin = self.ent_fin.get().strip()
        if ini not in self.grafo or fin not in self.grafo:
            messagebox.showwarning("Vértices inválidos", "Uno o ambos vértices no existen en G1.")
            return
        cola: Deque[List[str]] = deque([[ini]])
        visitados = {ini}
        while cola:
            camino = cola.popleft()
            ultimo = camino[-1]
            if ultimo == fin:
                self._escribir(
                    "BÚSQUEDA EN ANCHURA (BFS) — RUTA MÁS CORTA\n"
                    "======================================================================\n\n"
                    f"• Vértice origen  : {ini}\n"
                    f"• Vértice destino : {fin}\n"
                    f"• Ruta óptima     : {' -> '.join(camino)}\n"
                    f"• Longitud        : {len(camino) - 1} aristas"
                )
                return
            for vec in sorted(self.grafo[ultimo]):
                if vec not in visitados:
                    visitados.add(vec)
                    cola.append(camino + [vec])
        self._escribir(f"No existe una ruta que conecte a '{ini}' con '{fin}'.")

    def buscar_circuito(self) -> None:
        visitados: Set[str] = set()
        padre: Dict[str, Optional[str]] = {}

        for inicio in self.grafo:
            if inicio not in visitados:
                pila: List[Tuple[str, Optional[str]]] = [(inicio, None)]
                while pila:
                    u, p = pila.pop()
                    if u in visitados:
                        continue
                    visitados.add(u)
                    padre[u] = p
                    for v in sorted(self.grafo[u]):
                        if v == p:
                            continue
                        if v in visitados:
                            # Reconstruir ciclo
                            ciclo = [v, u]
                            curr = padre.get(u)
                            while curr is not None and curr != v:
                                ciclo.append(curr)
                                curr = padre.get(curr)
                            ciclo.append(v)
                            self._escribir(
                                "DETECCIÓN DE CIRCUITOS (DFS)\n"
                                "======================================================================\n\n"
                                f"• Circuito encontrado : {' -> '.join(ciclo)}\n"
                                f"• Longitud del ciclo  : {len(ciclo) - 1} aristas"
                            )
                            return
                        pila.append((v, u))
        self._escribir("El grafo es acíclico (Bosque / Árbol): no contiene circuitos.")

    def evaluar_euler(self) -> None:
        nodos_con_aristas = [v for v in self.grafo if len(self.grafo[v]) > 0]
        if not nodos_con_aristas:
            self._escribir("El grafo no tiene aristas (circuito trivial en vértices aislados).")
            return
        # Verificar conexidad en vértices de grado positivo y paridad
        inicio = nodos_con_aristas[0]
        visitados = {inicio}
        cola = deque([inicio])
        while cola:
            u = cola.popleft()
            for w in self.grafo[u]:
                if w not in visitados:
                    visitados.add(w)
                    cola.append(w)
        impares = [v for v in self.grafo if len(self.grafo[v]) % 2 != 0]

        if len(visitados) != len(nodos_con_aristas) or impares:
            self._escribir(
                "EVALUACIÓN DE CIRCUITO DE EULER\n"
                "======================================================================\n\n"
                "• Resultado: El grafo NO posee un circuito de Euler.\n"
                f"• Vértices con grado impar: {impares if impares else 'Ninguno (falla por desconexión)'}\n\n"
                "Condición necesaria y suficiente (Teorema de Euler):\n"
                "Todos los vértices con grado positivo deben pertenecer a una única\n"
                "componente conexa y tener grado estrictamente PAR."
            )
            return

        # Algoritmo de Hierholzer
        adj_copia = {u: sorted(list(vecs)) for u, vecs in self.grafo.items()}
        pila = [inicio]
        circuito: List[str] = []
        while pila:
            v = pila[-1]
            if adj_copia[v]:
                u = adj_copia[v].pop(0)
                adj_copia[u].remove(v)
                pila.append(u)
            else:
                circuito.append(pila.pop())
        circuito.reverse()
        self._escribir(
            "EVALUACIÓN DE CIRCUITO DE EULER (ALGORITMO DE HIERHOLZER)\n"
            "======================================================================\n\n"
            "• Condición: Todos los vértices tienen grado par y el grafo es conexo. [✓]\n"
            f"• Recorrido Euleriano:\n  {' -> '.join(circuito)}"
        )

    def buscar_hamilton(self) -> None:
        vertices = list(self.grafo.keys())
        n = len(vertices)
        if n == 0:
            self._escribir("El grafo no tiene vértices.")
            return
        if n > 10:
            self._escribir("Por complejidad factorial O(n!), esta versión admite hasta 10 vértices.")
            return

        camino_enc: Optional[List[str]] = None
        for orden in permutations(vertices):
            if all(orden[i + 1] in self.grafo[orden[i]] for i in range(n - 1)):
                camino_enc = list(orden)
                break

        ciclo_enc: Optional[List[str]] = None
        if n >= 3:
            primero = vertices[0]
            for orden in permutations(vertices[1:]):
                ciclo = [primero] + list(orden) + [primero]
                if all(ciclo[i + 1] in self.grafo[ciclo[i]] for i in range(len(ciclo) - 1)):
                    ciclo_enc = ciclo
                    break

        lineas = [
            "CAMINOS Y CICLOS DE HAMILTON (BÚSQUEDA EXHAUSTIVA)",
            "======================================================================",
            "",
            f"• Camino de Hamilton : {' -> '.join(camino_enc) if camino_enc else 'No existe'}",
            f"• Ciclo de Hamilton  : {' -> '.join(ciclo_enc) if ciclo_enc else 'No existe'}",
        ]
        self._escribir("\n".join(lineas))

    def comparar_isomorfismo(self) -> None:
        g1 = self.grafo
        g2 = self._parsear_grafo(self.ent_v2.get(), self.ent_a2.get())
        if g2 is None:
            return
        v1 = list(g1.keys())
        v2 = list(g2.keys())
        if len(v1) != len(v2):
            self._escribir("NO SON ISOMORFOS: Tienen diferente cantidad de vértices.")
            return
        grados1 = sorted(len(g1[u]) for u in v1)
        grados2 = sorted(len(g2[u]) for u in v2)
        if grados1 != grados2:
            self._escribir(
                "NO SON ISOMORFOS: Sus sucesiones gráficas (grados) no coinciden.\n"
                f"• Grados G1: {grados1}\n• Grados G2: {grados2}"
            )
            return

        for perm in permutations(v2):
            mapeo = dict(zip(v1, perm))
            es_iso = True
            for u in v1:
                if len(g1[u]) != len(g2[mapeo[u]]):
                    es_iso = False
                    break
                for w in g1[u]:
                    if mapeo[w] not in g2[mapeo[u]]:
                        es_iso = False
                        break
                if not es_iso:
                    break
            if es_iso:
                biyeccion = ", ".join(f"{a} ↦ {b}" for a, b in mapeo.items())
                self._escribir(
                    "VERIFICACIÓN DE ISOMORFISMO DE GRAFOS (G1 ≅ G2)\n"
                    "======================================================================\n\n"
                    "• Veredicto : [✓] LOS GRAFOS SON ISOMORFOS\n"
                    f"• Biyección que preserva adyacencia:\n  f = {{ {biyeccion} }}"
                )
                return
        self._escribir("VEREDICTO: Los grafos NO son isomorfos (no existe biyección estructural).")


# ==============================================================================
# MÓDULO 6: GRAFOS PLANOS, COLORACIÓN Y POLINOMIO CROMÁTICO
# ==============================================================================

class Modulo6GrafosPlanosColoracion(tk.Frame):
    def __init__(self, parent: tk.Widget) -> None:
        super().__init__(parent, bg="#f8fafc")
        self.ejemplos: Dict[str, Tuple[str, str]] = {
            "Ciclo C_4 (Plano, Bipartito)": ("A, B, C, D", "A-B, B-C, C-D, D-A"),
            "Grafo Completo K_4 (Plano, 4 caras)": ("A, B, C, D", "A-B, A-C, A-D, B-C, B-D, C-D"),
            "Grafo Rueda W_4 (Pirámide)": ("C, 1, 2, 3, 4", "1-2, 2-3, 3-4, 4-1, C-1, C-2, C-3, C-4"),
            "Kuratowski K_5 (No Plano)": (
                "1, 2, 3, 4, 5",
                "1-2, 1-3, 1-4, 1-5, 2-3, 2-4, 2-5, 3-4, 3-5, 4-5"
            ),
            "Kuratowski K_{3,3} (Grafo de Servicios - No Plano)": (
                "A1, A2, A3, B1, B2, B3",
                "A1-B1, A1-B2, A1-B3, A2-B1, A2-B2, A2-B3, A3-B1, A3-B2, A3-B3"
            ),
        }
        self._construir_ui()
        self.ejecutar_analisis_completo()

    def _construir_ui(self) -> None:
        header = tk.Label(
            self,
            text="MÓDULO 6: GRAFOS PLANOS, COLORACIÓN Y POLINOMIO CROMÁTICO P(G, k)",
            font=("Arial", 16, "bold"), bg="#3b0764", fg="white", pady=12
        )
        header.pack(fill="x")

        cuerpo = tk.Frame(self, bg="#f8fafc", padx=14, pady=10)
        cuerpo.pack(fill="both", expand=True)

        panel = tk.Frame(cuerpo, width=330, bg="#f3e8ff", padx=12, pady=12)
        panel.pack(side="left", fill="y")
        panel.pack_propagate(False)

        tk.Label(panel, text="Cargar Caso de Estudio Clásico:", font=("Arial", 10, "bold"), bg="#f3e8ff").pack(anchor="w")
        self.combo_ejemplos = ttk.Combobox(
            panel, values=list(self.ejemplos.keys()), state="readonly", font=("Arial", 10)
        )
        self.combo_ejemplos.current(1)
        self.combo_ejemplos.pack(fill="x", pady=(4, 6))
        self.combo_ejemplos.bind("<<ComboboxSelected>>", self._cargar_ejemplo)

        tk.Label(panel, text="Vértices:", font=("Arial", 10, "bold"), bg="#f3e8ff").pack(anchor="w")
        self.ent_v = tk.Entry(panel, font=("Arial", 10))
        self.ent_v.insert(0, "A, B, C, D")
        self.ent_v.pack(fill="x", pady=3)

        tk.Label(panel, text="Aristas (u-v):", font=("Arial", 10, "bold"), bg="#f3e8ff").pack(anchor="w")
        self.ent_a = tk.Entry(panel, font=("Arial", 10))
        self.ent_a.insert(0, "A-B, A-C, A-D, B-C, B-D, C-D")
        self.ent_a.pack(fill="x", pady=3)

        tk.Label(panel, text="Colores disponibles (k) a evaluar en P(G, k):", font=("Arial", 10, "bold"), bg="#f3e8ff").pack(anchor="w", pady=(6, 0))
        self.ent_k = tk.Entry(panel, font=("Arial", 10))
        self.ent_k.insert(0, "4")
        self.ent_k.pack(fill="x", pady=3)

        tk.Button(
            panel, text="Ejecutar Diagnóstico Completo", command=self.ejecutar_analisis_completo,
            bg="#6b21a8", fg="white", font=("Arial", 10, "bold"), pady=7
        ).pack(fill="x", pady=10)

        self.lienzo = tk.Canvas(panel, bg="white", height=230, highlightthickness=1, highlightbackground="#c084fc")
        self.lienzo.pack(fill="both", expand=True)

        zona = tk.Frame(cuerpo, bg="#f8fafc")
        zona.pack(side="right", fill="both", expand=True, padx=(14, 0))

        tk.Label(
            zona,
            text="Reporte Algebraico: Planaridad (Euler/Kuratowski), Coloración y Eliminación-Contracción:",
            font=("Arial", 11, "bold"), bg="#f8fafc"
        ).pack(anchor="w")

        self.consola = tk.Text(
            zona, font=("Consolas", 11), bg="#0f172a", fg="#f8fafc",
            padx=14, pady=14, wrap="word", state="disabled"
        )
        self.consola.pack(fill="both", expand=True, pady=(6, 0))

    def _cargar_ejemplo(self, _evento=None) -> None:
        nombre = self.combo_ejemplos.get()
        v, a = self.ejemplos[nombre]
        self.ent_v.delete(0, "end")
        self.ent_v.insert(0, v)
        self.ent_a.delete(0, "end")
        self.ent_a.insert(0, a)
        self.ejecutar_analisis_completo()

    def _dibujar_grafo_coloreado(self, g: Grafo, coloracion: Dict[str, int]) -> None:
        self.lienzo.update_idletasks()
        self.lienzo.delete("all")
        nodos = list(g.adyacencia.keys())
        if not nodos:
            return
        paleta = ["#ef4444", "#3b82f6", "#10b981", "#f59e0b", "#8b5cf6", "#ec4899", "#14b8a6"]
        w = max(self.lienzo.winfo_width(), 280)
        h = max(self.lienzo.winfo_height(), 210)
        cx, cy = w / 2, h / 2
        r = min(w, h) * 0.36
        pos = {}
        for i, v in enumerate(nodos):
            ang = -math.pi / 2 + (2 * math.pi * i / len(nodos))
            pos[v] = (cx + r * math.cos(ang), cy + r * math.sin(ang))

        for u, v in g.obtener_aristas():
            x1, y1 = pos[u]
            x2, y2 = pos[v]
            self.lienzo.create_line(x1, y1, x2, y2, fill="#64748b", width=2)

        for v, (x, y) in pos.items():
            c_idx = (coloracion.get(v, 1) - 1) % len(paleta)
            color_hex = paleta[c_idx]
            self.lienzo.create_oval(x - 16, y - 16, x + 16, y + 16, fill=color_hex, outline="#1e1b4b", width=2)
            self.lienzo.create_text(x, y, text=f"{v}\n(C{coloracion.get(v, 1)})", fill="white", font=("Arial", 8, "bold"))

    def ejecutar_analisis_completo(self) -> None:
        nombre = self.combo_ejemplos.get() or "Grafo Personalizado"
        g = Grafo(nombre)
        for v in [x.strip() for x in self.ent_v.get().split(",") if x.strip()]:
            g.agregar_vertice(v)
        if self.ent_a.get().strip():
            for par in self.ent_a.get().split(","):
                partes = par.strip().split("-")
                if len(partes) == 2:
                    g.agregar_arista(partes[0].strip(), partes[1].strip())

        try:
            k_eval = int(self.ent_k.get().strip())
        except ValueError:
            k_eval = 4

        rep = g.analizar_planaridad()
        wp = g.coloracion_welsh_powell()
        chi, col_exacta = g.coloracion_exacta()

        if len(g.obtener_aristas()) <= 16:
            polinomio = g.polinomio_cromatico()
            str_poli = str(polinomio)
            formas_k = polinomio.evaluar(k_eval)
            tabla_eval = "\n".join(
                f"   • P(G, {k}) = {polinomio.evaluar(k):,}" for k in range(1, 7)
            )
        else:
            str_poli = "(Omitido: |E| > 16 excede umbral de recursión de Eliminación-Contracción)"
            formas_k = 0
            tabla_eval = "   • Reduzca la cantidad de aristas para el cálculo simbólico exacto."

        self._dibujar_grafo_coloreado(g, col_exacta)

        euler_txt = (
            f"V - E + F = {rep.vertices} - {rep.aristas} + {rep.caras_euler} = "
            f"{rep.vertices - rep.aristas + (rep.caras_euler or 0)} (1 + C = {1 + rep.componentes_conexas})"
            if rep.es_plano else "No aplica (Grafo No Plano)"
        )

        reporte = (
            "========================================================================\n"
            f" 1. VERIFICACIÓN DE PLANARIDAD Y TEOREMA DE KURATOWSKI\n"
            "========================================================================\n"
            f"• ¿Es Grafo Plano?       : {'[✓] SÍ ES PLANO' if rep.es_plano else '[✗] NO ES PLANO'}\n"
            f"• Orden |V| y Tamaño |E| : V = {rep.vertices}, E = {rep.aristas}, Componentes C = {rep.componentes_conexas}\n"
            f"• Regiones / Caras (F)   : {rep.caras_euler if rep.caras_euler is not None else 'N/A'}\n"
            f"• Identidad de Euler     : {euler_txt}\n"
            f"• Justificación Formal   : {rep.motivo}\n\n"
            "========================================================================\n"
            " 2. COLORACIÓN DE VÉRTICES Y NÚMERO CROMÁTICO χ(G)\n"
            "========================================================================\n"
            f"• Número Cromático Exacto χ(G)    : {chi} colores (cumple Teorema de los 4 Colores si es plano)\n"
            f"• Asignación Óptima (Backtracking): {col_exacta}\n"
            f"• Heurística Voraz Welsh-Powell   : {wp} ({max(wp.values()) if wp else 0} colores usados)\n\n"
            "========================================================================\n"
            " 3. POLINOMIO CROMÁTICO P(G, k) = P(G - e, k) - P(G / e, k)\n"
            "========================================================================\n"
            f"• Expresión Algebraica Expandida:\n"
            f"  P(G, k) = {str_poli}\n\n"
            f"• Evaluación para k = {k_eval} colores : {formas_k:,} coloraciones propias válidas\n"
            f"• Tabla de Evaluaciones P(G, k) para k ∈ {{1..6}}:\n{tabla_eval}"
        )

        self.consola.config(state="normal")
        self.consola.delete("1.0", "end")
        self.consola.insert("end", reporte)
        self.consola.config(state="disabled")


# ==============================================================================
# MÓDULO 7: ÁRBOLES Y RECORRIDO DE ÁRBOLES (ABB + N-ARIOS)
# ==============================================================================

class Modulo7ArbolesRecorridos(tk.Frame):
    def __init__(self, parent: tk.Widget) -> None:
        super().__init__(parent, bg="#f8fafc")
        self.abb = ArbolBinarioBusqueda[int]()
        for d in [50, 30, 70, 20, 40, 60, 80, 15, 25, 65]:
            self.abb.insertar(d)
        self._construir_ui()
        self.actualizar_vista()

    def _construir_ui(self) -> None:
        header = tk.Label(
            self, text="MÓDULO 7: ÁRBOLES BINARIOS DE BÚSQUEDA (ABB), BALANCE AVL Y N-ARIOS",
            font=("Arial", 16, "bold"), bg="#14532d", fg="white", pady=12
        )
        header.pack(fill="x")

        cuerpo = tk.Frame(self, bg="#f8fafc", padx=14, pady=10)
        cuerpo.pack(fill="both", expand=True)

        panel = tk.Frame(cuerpo, width=300, bg="#dcfce7", padx=12, pady=12)
        panel.pack(side="left", fill="y")
        panel.pack_propagate(False)

        tk.Label(panel, text="Valor entero (Clave):", font=("Arial", 11, "bold"), bg="#dcfce7").pack(anchor="w")
        self.ent_val = tk.Entry(panel, font=("Arial", 12))
        self.ent_val.insert(0, "65")
        self.ent_val.pack(fill="x", pady=(4, 10))

        botones = [
            ("Insertar Nodo en ABB", self.insertar_nodo, "#15803d"),
            ("Buscar Clave y Trazar Ruta O(h)", self.buscar_nodo, "#1d4ed8"),
            ("Eliminar Nodo (3 Casos ABB)", self.eliminar_nodo, "#b91c1c"),
            ("Restaurar Árbol de Demostración", self.restaurar_demo, "#334155"),
            ("Demostración Árbol N-ario (Directorios)", self.mostrar_nario, "#6d28d9"),
        ]
        for txt, cmd, col in botones:
            tk.Button(
                panel, text=txt, command=cmd, bg=col, fg="white",
                font=("Arial", 10, "bold"), pady=6
            ).pack(fill="x", pady=4)

        tk.Label(
            panel, text="Representación Gráfica del ABB:",
            font=("Arial", 10, "bold"), bg="#dcfce7"
        ).pack(anchor="w", pady=(10, 4))

        self.canvas_arbol = tk.Canvas(panel, bg="white", highlightthickness=1, highlightbackground="#86efac")
        self.canvas_arbol.pack(fill="both", expand=True)
        self.canvas_arbol.bind("<Configure>", lambda e: self._dibujar_canvas_abb())

        zona = tk.Frame(cuerpo, bg="#f8fafc")
        zona.pack(side="right", fill="both", expand=True, padx=(14, 0))

        tk.Label(
            zona, text="Visualización ASCII, Recorridos DFS (Recursivo/Iterativo), BFS y Diagnóstico AVL:",
            font=("Arial", 11, "bold"), bg="#f8fafc"
        ).pack(anchor="w")

        self.consola = tk.Text(
            zona, font=("Consolas", 10), bg="#0f172a", fg="#f8fafc",
            padx=14, pady=12, wrap="word", state="disabled"
        )
        self.consola.pack(fill="both", expand=True, pady=(6, 0))

    def _leer_entero(self) -> Optional[int]:
        try:
            return int(self.ent_val.get().strip())
        except ValueError:
            messagebox.showwarning("Dato inválido", "Ingresa un número entero válido.")
            return None

    def insertar_nodo(self) -> None:
        v = self._leer_entero()
        if v is not None:
            self.abb.insertar(v)
            self.actualizar_vista(f"Se insertó la clave [{v}] respetando el invariante ABB.")

    def buscar_nodo(self) -> None:
        v = self._leer_entero()
        if v is not None:
            enc, ruta = self.abb.buscar(v)
            estado = "ENCONTRADO [✓]" if enc else "NO ENCONTRADO [✗]"
            self.actualizar_vista(
                f"Búsqueda de clave [{v}]: {estado} | Camino recorrido: {' -> '.join(map(str, ruta))}"
            )

    def eliminar_nodo(self) -> None:
        v = self._leer_entero()
        if v is not None:
            self.abb.eliminar(v)
            self.actualizar_vista(f"Se ejecutó la eliminación de la clave [{v}] (reemplazo por sucesor in-orden si tenía 2 hijos).")

    def restaurar_demo(self) -> None:
        self.abb = ArbolBinarioBusqueda[int]()
        for d in [50, 30, 70, 20, 40, 60, 80, 15, 25, 65]:
            self.abb.insertar(d)
        self.actualizar_vista("Árbol de demostración original restaurado.")

    def _dibujar_canvas_abb(self) -> None:
        self.canvas_arbol.delete("all")
        if not self.abb.raiz:
            return
        w = max(self.canvas_arbol.winfo_width(), 260)

        def _trazar(nodo: Optional[NodoBinario[int]], x: float, y: float, dx: float) -> None:
            if not nodo:
                return
            if nodo.izquierdo:
                self.canvas_arbol.create_line(x, y, x - dx, y + 48, fill="#475569", width=2)
                _trazar(nodo.izquierdo, x - dx, y + 48, max(dx / 1.9, 14))
            if nodo.derecho:
                self.canvas_arbol.create_line(x, y, x + dx, y + 48, fill="#475569", width=2)
                _trazar(nodo.derecho, x + dx, y + 48, max(dx / 1.9, 14))
            self.canvas_arbol.create_oval(x - 14, y - 14, x + 14, y + 14, fill="#16a34a", outline="#14532d", width=2)
            self.canvas_arbol.create_text(x, y, text=str(nodo.valor), fill="white", font=("Arial", 8, "bold"))

        _trazar(self.abb.raiz, w / 2, 24, w / 4.2)

    def actualizar_vista(self, mensaje_extra: str = "") -> None:
        self._dibujar_canvas_abb()
        pre_r = self.abb.pre_orden_recursivo()
        in_r = self.abb.in_orden_recursivo()
        post_r = self.abb.post_orden_recursivo()
        eq_iter = (
            pre_r == self.abb.pre_orden_iterativo()
            and in_r == self.abb.in_orden_iterativo()
            and post_r == self.abb.post_orden_iterativo()
        )
        bfs_plano, bfs_niveles = self.abb.recorrido_por_niveles_bfs()
        niveles_str = "\n".join(f"   • Nivel {i}: {niv}" for i, niv in enumerate(bfs_niveles))

        encabezado_extra = f">>> {mensaje_extra}\n\n" if mensaje_extra else ""
        texto = (
            f"{encabezado_extra}"
            "========================================================================\n"
            " 1. VISUALIZACIÓN JERÁRQUICA DEL ABB (Subárbol Der arriba ┌──, Izq abajo └──)\n"
            "========================================================================\n"
            f"{self.abb.renderizar_ascii()}\n\n"
            "========================================================================\n"
            " 2. RECORRIDOS EN PROFUNDIDAD (DFS) Y EN ANCHURA (BFS)\n"
            "========================================================================\n"
            f"• Pre-Orden  (Raíz -> Izq -> Der) : {pre_r}\n"
            f"• In-Orden   (Izq -> Raíz -> Der) : {in_r}  (Orden ascendente)\n"
            f"• Post-Orden (Izq -> Der -> Raíz) : {post_r}\n"
            f"• Equivalencia Recursivo/Iterativo: {'[✓] Coincidencia 100% verificada con pila explícita' if eq_iter else '[✗]'}\n\n"
            f"• BFS Por Niveles (Plano)         : {bfs_plano}\n"
            f"{niveles_str}\n\n"
            "========================================================================\n"
            " 3. DIAGNÓSTICO ESTRUCTURAL EN O(n)\n"
            "========================================================================\n"
            f"• Altura del árbol h(T)           : {self.abb.altura()}\n"
            f"• Nodos hoja (grado de salida 0)  : {self.abb.obtener_hojas()}\n"
            f"• ¿Cumple condición balanceo AVL? : {'[✓] Sí (|h_izq - h_der| <= 1 en todo nodo)' if self.abb.es_balanceado_avl() else '[✗] No (Requiere rotación AVL)'}"
        )
        self.consola.config(state="normal")
        self.consola.delete("1.0", "end")
        self.consola.insert("end", texto)
        self.consola.config(state="disabled")

    def mostrar_nario(self) -> None:
        raiz_fs = NodoNario("/proyecto_universitario")
        src = raiz_fs.agregar_hijo(NodoNario("src"))
        src.agregar_hijo(NodoNario("grafos.py"))
        src.agregar_hijo(NodoNario("arboles.py"))
        docs = raiz_fs.agregar_hijo(NodoNario("docs"))
        docs.agregar_hijo(NodoNario("informe_final.pdf"))

        self.actualizar_vista(
            f"ÁRBOL GENERAL N-ARIO (/proyecto_universitario) -> "
            f"Pre-Orden: {raiz_fs.pre_orden()} | Post-Orden: {raiz_fs.post_orden()}"
        )


# ==============================================================================
# CONTROLADOR PRINCIPAL — NAVEGACIÓN SECUENCIAL EN EL ORDEN EXACTO SOLICITADO
# ==============================================================================

class SuiteMatematicaDiscretaApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Suite Universitaria de Matemática Discreta — 7 Programas Unificados")
        self.root.geometry("1180x780")
        self.root.minsize(1020, 680)

        self.titulos_ordenados = [
            "1. Mate Discreta (Inducción Matemática)",
            "2. Import tkinter (Combinatoria y Conteo)",
            "3. Sistema Aritmética (Teoría de Números)",
            "4. Sistema de Grafos (Visualizador y Matrices)",
            "5. Grafos (Rutas, Euler, Hamilton e Isomorfismo)",
            "6. Grafos Planos, Coloración y Polinomios",
            "7. Árboles y Recorrido de Árboles",
        ]
        self.clases_modulos = [
            Modulo1MateDiscreta,
            Modulo2CombinatoriaTkinter,
            Modulo3SistemaAritmetica,
            Modulo4SistemaGrafos,
            Modulo5TeoriaGrafos,
            Modulo6GrafosPlanosColoracion,
            Modulo7ArbolesRecorridos,
        ]
        self.indice_actual = 0

        self._construir_barra_superior()
        self.contenedor = tk.Frame(self.root, bg="#f8fafc")
        self.contenedor.pack(fill="both", expand=True)
        self._construir_barra_inferior()

        self.instancias: List[tk.Frame] = [
            clase(self.contenedor) for clase in self.clases_modulos
        ]
        self.mostrar_modulo(0)

    def _construir_barra_superior(self) -> None:
        barra = tk.Frame(self.root, bg="#020617", padx=14, pady=8)
        barra.pack(fill="x")

        tk.Label(
            barra, text="SECUENCIA DE PROGRAMAS:",
            font=("Arial", 10, "bold"), bg="#020617", fg="#94a3b8"
        ).pack(side="left", padx=(0, 8))

        self.combo_modulos = ttk.Combobox(
            barra, values=self.titulos_ordenados, state="readonly",
            width=45, font=("Arial", 10, "bold")
        )
        self.combo_modulos.pack(side="left", padx=4)
        self.combo_modulos.bind(
            "<<ComboboxSelected>>",
            lambda e: self.mostrar_modulo(self.combo_modulos.current())
        )

        self.lbl_progreso = tk.Label(
            barra, text="Paso 1 de 7", font=("Arial", 10, "bold"),
            bg="#020617", fg="#38bdf8"
        )
        self.lbl_progreso.pack(side="right", padx=10)

    def _construir_barra_inferior(self) -> None:
        pie = tk.Frame(self.root, bg="#0f172a", padx=16, pady=10)
        pie.pack(fill="x", side="bottom")

        self.btn_anterior = tk.Button(
            pie, text="◀  Programa Anterior", command=self.anterior_modulo,
            bg="#334155", fg="white", font=("Arial", 11, "bold"), padx=16, pady=6
        )
        self.btn_anterior.pack(side="left")

        self.lbl_pie = tk.Label(
            pie, text="", font=("Arial", 11, "bold"), bg="#0f172a", fg="#e2e8f0"
        )
        self.lbl_pie.pack(side="left", expand=True)

        self.btn_siguiente = tk.Button(
            pie, text="Siguiente Programa  ▶", command=self.siguiente_modulo,
            bg="#2563eb", fg="white", font=("Arial", 11, "bold"), padx=16, pady=6
        )
        self.btn_siguiente.pack(side="right")

    def mostrar_modulo(self, indice: int) -> None:
        for frame in self.instancias:
            frame.pack_forget()

        self.indice_actual = indice
        self.instancias[indice].pack(fill="both", expand=True)
        self.combo_modulos.current(indice)
        self.lbl_progreso.config(text=f"Programa {indice + 1} de {len(self.instancias)}")
        self.lbl_pie.config(text=f"Activo: {self.titulos_ordenados[indice]}")

        self.btn_anterior.config(state="normal" if indice > 0 else "disabled")
        if indice < len(self.instancias) - 1:
            sig_nombre = self.titulos_ordenados[indice + 1].split("(")[0].strip()
            self.btn_siguiente.config(
                state="normal",
                text=f"Siguiente: {sig_nombre}  ▶",
                bg="#2563eb"
            )
        else:
            self.btn_siguiente.config(
                state="disabled",
                text="Fin del Recorrido (Programa 7/7)",
                bg="#475569"
            )

    def siguiente_modulo(self) -> None:
        if self.indice_actual < len(self.instancias) - 1:
            self.mostrar_modulo(self.indice_actual + 1)

    def anterior_modulo(self) -> None:
        if self.indice_actual > 0:
            self.mostrar_modulo(self.indice_actual - 1)


if __name__ == "__main__":
    ventana_principal = tk.Tk()
    app = SuiteMatematicaDiscretaApp(ventana_principal)
    ventana_principal.mainloop()