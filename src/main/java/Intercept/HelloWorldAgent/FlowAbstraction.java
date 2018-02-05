package Intercept.HelloWorldAgent;


import soot.Unit;

public class FlowAbstraction {
	private final Unit source;
	private final Boolean isTrue;
	
	public FlowAbstraction(Unit source,Boolean isTrue) {
		super();
		this.source = source;
		this.isTrue = isTrue;
	}

	public Unit getSource() {
		return source;
	}


	public Boolean isTrue() {
		return isTrue;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((source == null) ? 0 : source.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || !(obj instanceof FlowAbstraction))
			return false;
		FlowAbstraction other = (FlowAbstraction) obj;
		if (source == null) {
			if (other.source != null)
				return false;
		} else if (!source.equals(other.source))
			return false;
		if (isTrue == null) {
			if (other.isTrue != null)
				return false;
		} else if (!isTrue.equals(other.isTrue))
			return false;
		return true;
	}
}
