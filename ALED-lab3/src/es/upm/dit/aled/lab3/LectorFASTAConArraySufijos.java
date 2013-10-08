package es.upm.dit.aled.lab3;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class LectorFASTAConArraySufijos extends LectorFASTA {
    protected int[] sufijos;

    private int compara(int index1, int index2, int len) {
    	for (int i=0; i < len; i++) {
    		if (contenido[index1+i] < contenido[index2+i]) return -1;
    		if (contenido[index1+i] > contenido[index2+i]) return 1;
    	}
    	return 0;
    }
    
    private int compara(int index1, int index2) {
    	int len=Math.min(bytesValidos-index1, bytesValidos-index2);
    	for (int i=0; i < len; i++) {
    		if (contenido[index1+i] < contenido[index2+i]) return -1;
    		if (contenido[index1+i] > contenido[index2+i]) return 1;
    	}
    	return 0;
    }
    
    private static void intercambia(int x[], int a, int b) {
		int t = x[a];
		x[a] = x[b];
		x[b] = t;
    }
    
    private int med3(int x[], int a, int b, int c) {
    	int ab=Math.min(bytesValidos-a,bytesValidos-b);
    	int ac=Math.min(bytesValidos-a,bytesValidos-c);
    	int bc=Math.min(bytesValidos-b,bytesValidos-c);
    	return (compara(a,b,ab) < 0 ?
    	    (compara(b,c,bc) < 0 ? b : compara(a,c,ac) < 0 ? c : a) :
    	    (compara(b,c,bc) > 0 ? b : compara(a,c,ac) > 0 ? c : a));
	/*	return (x[a] < x[b] ?
			(x[b] < x[c] ? b : x[a] < x[c] ? c : a) :
			(x[b] > x[c] ? b : x[a] > x[c] ? c : a)); */
    }
    
    private void vecintercambia(int x[], int a, int b, int n) {
		for (int i=0; i<n; i++, a++, b++)
		    intercambia(x, a, b);
    }
    
    private void ordena(int off, int len) {
    	if (len < 7) {
    	    for (int i=off; i<len+off; i++)
    	    	for (int j=i; j>off && (compara(sufijos[j-1],sufijos[j],bytesValidos-j) > 0); j--)
//     		for (int j=i; j>off && x[j-1]>x[j]; j--)
    	    		intercambia(sufijos, j, j-1);
    	    return;
    	}

    	// Choose a partition element, v
    	int m = off + (len >> 1);       // Small arrays, middle element
    	if (len > 7) {
    	    int l = off;
    	    int n = off + len - 1;
    	    if (len > 40) {        // Big arrays, pseudomedian of 9
    		int s = len/8;
    		l = med3(sufijos, l,     l+s, l+2*s);
    		m = med3(sufijos, m-s,   m,   m+s);
    		n = med3(sufijos, n-2*s, n-s, n);
    	    }
    	    m = med3(sufijos, l, m, n); // Mid-size, med of 3
    	}
    	int v = sufijos[m];

    	// Establish Invariant: v* (<v)* (>v)* v*
    	int a = off, b = a, c = off + len - 1, d = c;
    	while(true) {
    	    int cmp;
    	    while (b <= c && (cmp=compara(sufijos[b],v)) < 1) {
    		if (cmp == 0)
    		    intercambia(sufijos, a++, b);
    		b++;
    	    }
    	    while (c >= b && (cmp=compara(sufijos[c],v)) > -1) {
    		if (cmp == 0)
    		    intercambia(sufijos, c, d--);
    		c--;
    	    }
    	    if (b > c)
    		break;
    	    intercambia(sufijos, b++, c--);
    	}

    	// Swap partition elements back to middle
    	int s, n = off + len;
    	s = Math.min(a-off, b-a  );  vecintercambia(sufijos, off, b-s, s);
    	s = Math.min(d-c,   n-d-1);  vecintercambia(sufijos, b,   n-s, s);

    	// Ordena recursivamente
    	if ((s = b-a) > 1)
    	    ordena(off, s);
    	if ((s = d-c) > 1)
    	    ordena(n-s, s);
    }
    
    public void ordena() {
    	ordena(0,bytesValidos);
    }
    
    public LectorFASTAConArraySufijos(byte[] text, int bytesValidos, boolean doSort) {
        super(text,bytesValidos);
        this.sufijos = new int[bytesValidos];
        for (int i = 0; i < bytesValidos; i++)
            sufijos[i] = i;
        if (doSort) ordena(0,bytesValidos);
    }

    // length of string
    public int length() { return sufijos.length; }

    // indice del contenido al que apunta la posicion i de la tabla de sufijos
    public int index(int i) { return sufijos[i]; }


    // tamano maximo de de prefijo comun de sufijos(i) y sufijos(i-1)
    public int lcp(int i) {
        return lcp(sufijos[i], sufijos[i-1]);
    }

    // maximo comun prefijo de s y t
    private int lcp(int s, int t) {
        int N = Math.min(bytesValidos-s, bytesValidos-t);
        for (int i = 0; i < N; i++) {
            if (contenido[s+i] != contenido[t+i]) return i;
        }
        return N;
    }

    public String select(int i) {
        return new String(contenido,sufijos[i],bytesValidos-sufijos[i]);
    }

    // numero de sufijos estrictamente menor que buscado
    public int rank(String buscado) {
        int lo = 0, hi = sufijos.length - 1;
        while (lo <= hi) {
            int mid = lo + (hi - lo) / 2;
            int cmp = compara(buscado, sufijos[mid]);
            if      (cmp < 0) hi = mid - 1;
            else if (cmp > 0) lo = mid + 1;
            else return mid;
        }
        return lo;
    } 

    // compara buscado y el string que referencia sufijo
    private int compara(String query, int sufijo) {
    	int indiceSufijo=sufijos[sufijo];
        int N = Math.min(query.length(), bytesValidos-indiceSufijo);
        for (int i = 0; i < N; i++) {
            if (query.charAt(i) < contenido[indiceSufijo+i]) return -1;
            if (query.charAt(i) > contenido[indiceSufijo+i]) return +1;
        }
        return query.length() - bytesValidos-indiceSufijo;
    }
    
	public void imprime() {
        System.out.println("  i ind lcp rnk  select");
        System.out.println("---------------------------");

        for (int i = 0; i < bytesValidos; i++) {
            int index = index(i);
            String ith = "\"" + new String(contenido,index, Math.min(50, bytesValidos-index)) + "\"";
            int rank = rank(select(i));
            if (i == 0) {
            	System.out.printf("%3d %3d %3s %3d  %s\n", i, index, "-", rank, ith);
            }
            else {
                int lcp  = lcp(i);
                System.out.printf("%3d %3d %3d %3d  %s\n", i, index, lcp, rank, ith);
            }
        }
	}
	
	public void salvaSufijos(PrintWriter dout) throws IOException {
		int len = length();
		dout.println(len);
		for (int i=0; i < len; i++) {
			dout.print(i);
			dout.print(" ");
			dout.print(index(i));
			dout.println();
		}
		dout.flush();
	}
	
	public void cargaSufijos(BufferedReader di) throws IOException {
		String lenS=di.readLine();
		if (lenS == null || lenS.length() <= 0)
			throw new IOException("Suffix file format error");
		int len=Integer.parseInt(lenS);
		if (len != sufijos.length)
			throw new IOException("Suffix file format error");
		for (int i=0; i < len; i++) {
			String line=di.readLine();
			Scanner scn=new Scanner(line);
			int j=scn.nextInt();
			int index=scn.nextInt();
			sufijos[i]=index;
		}
	}
	
    // crea una array de suficjos a partir del nombre fichero que lo continene. 
    // Si ficheroSufijos!=null utiliza ese fichero para inicializar los sufijos, sino hay que calcularlos
    public LectorFASTAConArraySufijos(String ficheroCromosoma, String ficheroSufijos) {
    	super(ficheroCromosoma);
		if (ficheroSufijos != null) {
	        this.sufijos = new int[bytesValidos];
	        for (int i = 0; i < bytesValidos; i++)
	            sufijos[i] = i;
	    	File f=new File(ficheroSufijos);
	    	Reader fis;
			try {
				fis = new FileReader(f);
		    	BufferedReader fid=new BufferedReader(fis);
				cargaSufijos(fid);
				fis.close();
			} catch (FileNotFoundException e) {
				e.printStackTrace();
				return;
			} catch (IOException e) {
				e.printStackTrace();
				return;
			}
		} else {
	        this.sufijos = new int[bytesValidos];
	        for (int i = 0; i < bytesValidos; i++)
	            sufijos[i] = i;
	        ordena(0,bytesValidos);
	    	File f=new File("suf_"+ficheroCromosoma+"suf");
	    	FileOutputStream fis;
			try {
				fis = new FileOutputStream(f);
		    	PrintWriter fid=new PrintWriter(fis);
		    	salvaSufijos(fid);
		    	fis.close();
			} catch (FileNotFoundException e) {
				e.printStackTrace();
				return;
			} catch (IOException e) {
				e.printStackTrace();
				return;
			}
		}
    }
    
    public List<Integer> buscar(byte[] patron) {
    	// TODO
    	return null;
    }
    
    public static void main(String[] args) {
    	String sufijos=null;
    	byte[] patron=null;
    	if (args.length > 2) {
    		sufijos=args[1];
    		patron=args[2].getBytes();
    	} else
    	if (args.length > 1)
    		patron=args[1].getBytes();
    	LectorFASTA cr = new LectorFASTAConArraySufijos(args[0],sufijos);
    	// ((LectorFASTAConArraySufijos) cr).imprime();
    	if (patron != null) {
	    	List<Integer> posiciones=cr.buscar(patron);
	    	if (posiciones.size() > 0)
		    	for (Integer pos : posiciones)
		    		System.out.println("Encontrado "+args[1]+" en "+pos+" : "+new String(cr.contenido, pos, args[1].length()));
	    	else System.out.println("No he encontrado : "+args[1]+" en ningun sitio");
    	}
    }
}
