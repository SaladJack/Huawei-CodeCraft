package com.filetool.model;

import java.util.ArrayList;

public class Vertex {
	public boolean bVisited;// 是否被访问过
	public Object oValue;// 顶点的值
	public ArrayList<Integer> visitedVertexIdList;

	public Vertex() {
		this.bVisited = false;
		this.oValue = "";
		this.visitedVertexIdList = new ArrayList<Integer>();
	}

	public Vertex(String name) {
		this.bVisited = false;
		this.oValue = name;
		this.visitedVertexIdList = new ArrayList<Integer>();
	}

	public void ResetVisitedIdList() {
		if (this.visitedVertexIdList != null) {
			for (Integer nVertexId : visitedVertexIdList) {
				nVertexId = 0;
			}
		} else {
			this.visitedVertexIdList = new ArrayList<Integer>();
		}
	}
}
}
}
}