package es.upm.dit.aled.lab2;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class LaberintoWeiss extends Laberinto {

    private static int ARRIBA = 1;
    private static int DERECHA = 2;
    private static int ABAJO = 4;
    private static int IZQUIERDA = 8;
    
    public static class Pared {
        public int fila, col;
        public int direccion;

        public Pared(int fila, int col, int direccion) {
                this.fila = fila;
                this.col = col;
                this.direccion = direccion;
        }
    }
    
	public LaberintoWeiss(int n) {
		super(n);
	}
	
	@Override
	protected void generar() {
        List<Pared> paredes = new ArrayList<Pared>(); // Lista de paredes levantadas
        for (int x = 1; x <= N; x++) {
                for (int y = 1; y <= N; y++) {
                        if (x > 1) {
                                paredes.add(new Pared(x,y,IZQUIERDA));
                        }
                        if (y < N) {
                        		paredes.add(new Pared(x,y,ARRIBA));
                        }
                }
        }
        // Conjuntos de posiciones que no estan comunicados. 
        // Inicialmente ninguno esta comunicado
        IDisjointSet diset = new ArrayDisjointSet(N*N);
        
        // TODO aqui va el algoritmo del enunciado de la practica
	}
	
    public static void main(String[] args) {
        int N = Integer.parseInt(args[0]);
        Laberinto laberinto = new LaberintoWeiss(N);
        StdDraw.show(0);
        laberinto.dibuja();
        laberinto.resolver();
    }
}
