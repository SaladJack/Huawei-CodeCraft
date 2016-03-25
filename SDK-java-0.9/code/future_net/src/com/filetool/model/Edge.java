package com.filetool.model;

public class Edge {
	public String strSerialNo;// 在拓扑结构中边的标号
	public int nSourceIdInMatrix;// 在邻接矩阵中起点的编号
	public int nSourceIdInTopo;// 拓扑结构中起点的编号
	public int nDestIdInMatrix;// 在邻接矩阵中尾端顶点的编号
	public int nDestIdInTopo;// 在拓扑结构中尾端顶点的编号
	public int nWeight;// 权值

	public Edge() {
		this.Reset();
	}

	public void Reset() {
		strSerialNo = "-1";
		nSourceIdInMatrix = -1;
		nSourceIdInTopo = -1;
		nDestIdInMatrix = -1;
		nDestIdInTopo = -1;
		nWeight = -1;
	}
}