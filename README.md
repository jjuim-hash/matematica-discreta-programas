# Programas de Matemática Discreta

Este proyecto reúne siete módulos para practicar temas de Matemática Discreta. Está hecho en Python y usa Tkinter para mostrar ventanas, botones y resultados.

Los siete módulos están dentro del mismo archivo. Para usarlos, se abre el programa y se elige el tema desde el menú de arriba o con los botones para avanzar y regresar.

## ¿Qué incluye?

1. **Inducción matemática:** ejemplos y demostraciones para repasar el tema.
2. **Combinatoria y conteo:** principio multiplicativo, permutaciones y combinaciones.
3. **Aritmética:** factorización, máximo común divisor, división y algoritmo de Euclides.
4. **Sistema de grafos:** construcción visual, listas y matrices de adyacencia y grados de los vértices.
5. **Teoría de grafos:** rutas y recorridos, Euler, Hamilton e isomorfismo.
6. **Grafos planos y coloración:** análisis de planaridad, coloración y polinomios cromáticos.
7. **Árboles:** insertar, buscar y eliminar valores en un árbol binario de búsqueda, ver recorridos y revisar su balance. También incluye un ejemplo de árbol n-ario.

## Archivos

- `Codigos matematica discreta.py`: contiene todo el código de los siete módulos.
- `README.md`: explica de qué trata el proyecto y cómo abrirlo.

## Lo que necesitás

- Python 3.10 o superior como versión recomendada.
- Tkinter disponible en tu instalación de Python.
- Una computadora con entorno gráfico para abrir la ventana.

El código usa bibliotecas de Python; no necesita paquetes externos de pip.

## Cómo abrirlo

1. Descargá el repositorio desde **Code → Download ZIP**.
2. Extraé el archivo ZIP.
3. Abrí la carpeta en Visual Studio Code o una terminal.
4. Ejecutá:

```bash
python "Codigos matematica discreta.py"
```

En Windows también podés probar:

```bash
py "Codigos matematica discreta.py"
```

Si tu sistema usa el comando `python3`, usalo en lugar de `python`.

Para comprobar que Tkinter está disponible, ejecutá `python -m tkinter`. Debería abrirse una ventana de prueba. Si aparece un error indicando que falta Tkinter, necesitás agregar el soporte Tcl/Tk a tu instalación de Python.

## Cómo usarlo

Elegí uno de los siete temas en la lista de arriba. Ingresá los datos que pide cada módulo y usá sus botones para ver los resultados. También podés cambiar de tema con los botones de la parte inferior.

Como ejemplo, en combinaciones podés usar 5 elementos y elegir 2: el resultado es 10 combinaciones.

## Algunas aclaraciones

Es un proyecto de estudio. Los cálculos más pesados de grafos pueden tardar cuando hay muchos vértices; conviene empezar con ejemplos pequeños. El análisis de planaridad implementado tiene limitaciones y no garantiza detectar todos los grafos no planos.

El archivo de código se conserva tal como fue entregado. Este repositorio agrega únicamente la explicación del README.

Para ejecutarlo hay que descargarlo y abrirlo con Python: GitHub permite ver y descargar el código, pero no abre la ventana de Tkinter en el navegador.
