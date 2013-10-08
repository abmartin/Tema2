package es.upm.dit.aled.lab3;

class BytesLeidos {
	public byte[] contenido;
	public int byteValidos;
	
	public BytesLeidos(byte[] contenido, int byteValidos) {
		this.contenido=contenido;
		this.byteValidos=byteValidos;
	}
	
	public byte[] getContenido() {
		return contenido;
	}
	
	public int getBytesValidos() {
		return byteValidos;
	}
}
