class AddQuestionIndex < ActiveRecord::Migration[5.0]
  def change
        add_column :questions, :index, :integer
  end
end
