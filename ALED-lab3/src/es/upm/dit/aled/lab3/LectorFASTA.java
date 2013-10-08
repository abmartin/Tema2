package es.upm.dit.aled.lab3;

import java.io.BufferedReader;
import java.io.DataInput;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;

public class LectorFASTA {

    protected byte[] contenido;
    protected int bytesValidos;
    
    public LectorFASTA(byte[] text, int byteValidos) {
    	contenido=text;
    	this.bytesValidos=byteValidos;
    }

    protected BytesLeidos leeFichero(String fileName) throws IOException {
    	File f=new File(fileName);
    	FileInputStream fis=new FileInputStream(f);
    	DataInput fid=new DataInputStream(fis);
		long len=(int) fis.getChannel().size();
		if (len > Integer.MAX_VALUE) {
			fis.close();
			throw new IOException("El fichero "+fileName+" es muy grande. No podemos representarlo con un array.");
		}
    	byte[] contents=new byte[(int) len];
    	int bytesRead=0;
    	int numRead=0;
    	String line;
    	while ((line=fid.readLine()) != null) {
    		line=line.toUpperCase();
    		numRead=line.length();
    		byte[] newData=line.getBytes();
    		for (int i=0; i < numRead; i++)
    			contents[bytesRead+i]=newData[i];
    		bytesRead+=numRead;
    	}
	    fis.close();
	    return new BytesLeidos(contents,bytesRead);
    }
    
    public String getSecuencia(int posicionInicial, int tamano) {
    	if (posicionInicial+tamano >= bytesValidos)
    		return null;
    	return new String(contenido,posicionInicial,tamano);
    }
    
    // crea un cromosoma a partir del fichero
    public LectorFASTA(String ficheroCromosoma) {
    	BytesLeidos rb=null;
		try {
			rb = leeFichero(ficheroCromosoma);
			
		} catch (IOException e) {
			e.printStackTrace();
			return;
		}
    	contenido=rb.getContenido();
    	this.bytesValidos=rb.getBytesValidos();
    }

    private boolean compara(byte[] patron, int posicionAComparar) throws FASTAException {
    	if (posicionAComparar+patron.length > bytesValidos)
    		throw new FASTAException("patron se sale del fichero FASTA");
		boolean fallo=false;
		for (int j=0; j < patron.length; j++)
			if (patron[j] != contenido[posicionAComparar+j] && patron[j] != 'N') {
				fallo=true;
			}
		return !fallo;
    }
    
    // buscar las posiciones donde encontramos el patron en el cromosoma
    public List<Integer> buscar(byte[] patron) {
    	// TODO
    	return null;
    }
    
    public static void main(String[] args) {
    	LectorFASTA cr = new LectorFASTA(args[0]);
    	int n=0;
    	for (int i=0; i < cr.bytesValidos; i++) 
    		if ((char) cr.contenido[i] == 'N')
    			n++;
    	if (args.length == 1) return;
    	List<Integer> posiciones=cr.buscar(args[1].getBytes());
    	if (posiciones.size() > 0)
	    	for (Integer pos : posiciones)
	    		System.out.println("Encontrado "+args[1]+" en "+pos+" : "+new String(cr.contenido, pos, args[1].length()));
    	else System.out.println("No he encontrado : "+args[1]+" en ningun sitio");
    }
}
