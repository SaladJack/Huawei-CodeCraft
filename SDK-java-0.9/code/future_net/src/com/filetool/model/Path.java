package com.filetool.model;

import java.util.ArrayList;

public class Path {
	public ArrayList<Integer> listSerialVertexId;// ��·���ϵĶ���
	public int nPathDistance;// ��·�����ܳ���

	public Path() {
		listSerialVertexId = new ArrayList<Integer>();
		nPathDistance = Integer.MAX_VALUE;// ·������ʼ��Ϊ����Զ
	}

	// ��ø�·�������˽ṹ�б�ʾ
	public String GetPathInTopo(ArrayList<Edge> edgeList) {
		if (edgeList != null && edgeList.size() > 0) {
			ArrayList<String> edgeIdList = new ArrayList<String>();
			for (int i = 0; i < this.listSerialVertexId.size() - 1; i++) {
				for (Edge edge : edgeList) {
					if (listSerialVertexId.get(i) == edge.nSourceIdInMatrix
							&& listSerialVertexId.get(i + 1) == edge.nDestIdInMatrix) {
						edgeIdList.add(edge.strSerialNo);
						break;
					}
				}
			}
			String strPathInTopo = "";
			for (String strEdgeId : edgeIdList) {
				strPathInTopo += strEdgeId;
				if (strEdgeId != edgeIdList.get(edgeIdList.size() - 1)) {
					strPathInTopo += "|";
				}
			}
			return strPathInTopo;
		} else {
			return "";
		}

	}

	// ·���Ƿ������
	public boolean ContainFixedVertexList(ArrayList<Integer> fixedVertexList) {
		if (fixedVertexList != null) {
			ArrayList<Integer> queue = new ArrayList<Integer>();
			for (Integer n : this.listSerialVertexId) {
				if (fixedVertexList.contains(n)) {
					queue.add(n);
				}
			}
			if (queue.size() == fixedVertexList.size()) {
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
	}

}